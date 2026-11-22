(ns afterglow.render.atmosphere.calibration
  "Fit a stationary sightline from linear camera contrast and held nozzle flows.
  Optical depth is dimensionless. The fit uses metres, seconds and cubic metres.")

(defn- finite? [x] (and (number? x) (Double/isFinite (double x))))
(defn- check [condition message]
  (when-not condition (throw (ex-info message {:component :fog-calibration}))))

(defn validate-sample! [{:keys [elapsed-ms bright dark phase] :as reading}]
  (check (and (finite? elapsed-ms) (<= 0 elapsed-ms 7200000)
              (every? #(and (finite? %) (<= 0 % 1)) [bright dark])
              (> bright dark) (#{:baseline :active :clearing} phase))
         "Invalid stationary camera sample")
  reading)

(defn- median [xs]
  (let [v (vec (sort xs)) i (quot (count v) 2)]
    (if (odd? (count v)) (double (v i)) (* 0.5 (+ (v i) (v (dec i)))))))

(defn- optical-observations [samples path-m]
  (let [samples (mapv validate-sample! samples)
        phases (partition-by :phase samples)
        contrast #(- (:bright %) (:dark %))
        baseline (mapv contrast (first phases))]
    (check (and (= [:baseline :active :clearing] (mapv (comp :phase first) phases))
                (apply < (map :elapsed-ms samples))
                (every? true? (map >= (map count phases) [4 4 6])))
           "Capture a clear reference, a fog burst, and its clearing tail in that order")
    (let [reference (median baseline)]
      (check (and (> reference 0.04)
                  (< (- (apply max baseline) (apply min baseline)) (* 0.10 reference)))
             "The clear reference needs more contrast or a steadier light")
      (mapv (fn [s] (assoc s :density (/ (max 0.0 (- (Math/log (/ (contrast s) reference)))) path-m)))
            samples))))

(defn- tail-fit [observations]
  (let [clearing (filterv #(= :clearing (:phase %)) observations)
        peak (apply max-key :density clearing)
        tail (filterv #(and (>= (:elapsed-ms %) (:elapsed-ms peak))
                            (> (:density %) (* 0.05 (:density peak)))) clearing)
        xs (mapv #(/ (- (:elapsed-ms %) (:elapsed-ms peak)) 1000.0) tail)
        ys (mapv #(Math/log (:density %)) tail)]
    (check (and (>= (count tail) 5) (>= (peek xs) 3)
                (> (:density peak) 0.003)
                (< (:density (peek tail)) (* 0.78 (:density peak))))
           "Keep scanning until the mixed fog has clearly fallen from its peak")
    (let [mean #(/ (reduce + 0.0 %) (count %))
          mx (mean xs) my (mean ys)
          dx (mapv #(- % mx) xs) dy (mapv #(- % my) ys)
          slope (/ (reduce + (map * dx dy)) (reduce + (map * dx dx)))
          residual (reduce + (map (fn [x y] (let [d (- y (* slope x))] (* d d))) dx dy))
          score (- 1.0 (/ residual (reduce + (map * dy dy))))
          half-life (/ (- (Math/log 2.0)) slope)]
      (check (and (finite? half-life) (<= 0.1 half-life 86400) (> score 0.75))
             "Clearing does not follow a steady decay; check the sightline and repeat")
      {:clearance-half-life-s half-life :r-squared score})))

(defn- schedule [observations flows]
  (let [events (reduce (fn [m {:keys [elapsed-ms density]}] (assoc-in m [elapsed-ms :reading] density))
                       (sorted-map) observations)
        events (reduce (fn [m {:keys [elapsed-ms flow-m3-s]}] (assoc-in m [elapsed-ms :flow] flow-m3-s))
                       events flows)]
    (loop [pairs (seq events) t 0.0 q 0.0 rows []]
      (if-let [[ms {:keys [reading flow]}] (first pairs)]
        (recur (next pairs) ms (or flow q) (conj rows [(/ (- ms t) 1000.0) q reading]))
        rows))))

(defn- fit-rates [timeline volume half-life mixing total-variance]
  ;; The local plume and room total have exact first-order responses to a held
  ;; pump. Fit extinction as one linear coefficient for each pair of rates.
  (let [k (/ (Math/log 2) half-life) km (+ k (/ 1.0 mixing))]
    (loop [i 0 total 0.0 local 0.0 xx 0.0 xy 0.0 yy 0.0]
      (if (= i (count timeline))
        (when (pos? xx)
          (let [coefficient (/ xy xx)
                rss (max 0.0 (- yy (* xy coefficient)))]
            {:extinction-per-m coefficient :mixing-seconds mixing :clearance-half-life-s half-life
             :r-squared (- 1.0 (/ rss total-variance))}))
        (let [[dt q reading] (nth timeline i)
              next-volume (fn [mass rate]
                            (let [delta (Math/expm1 (- (* dt rate)))]
                              (+ (* mass (+ 1.0 delta)) (* q (/ (- delta) rate)))))
              total (next-volume total k) local (next-volume local km)
              x (/ (- total local) volume)]
          (if (nil? reading)
            (recur (inc i) total local xx xy yy)
            (recur (inc i) total local (+ xx (* x x)) (+ xy (* x reading)) (+ yy (* reading reading)))))))))

(defn fit
  "Fit an effective half-life including ventilation and fluid losses. With one
  metered nozzle add the mixing time and optical extinction of rated fog.
  With an unmetered burst, only the clearing tail supplies a defensible fit."
  [{:keys [samples flows volume-m3 path-m]}]
  (check (and (finite? path-m) (<= 0.1 path-m 1000) (finite? volume-m3) (pos? volume-m3))
         "Expected a measured sightline distance and a positive room volume")
  (check (and (vector? samples) (<= 14 (count samples) 7201)
              (or (nil? flows)
                  (and (vector? flows) (<= (count flows) 8192)
                       (every? (fn [{:keys [elapsed-ms flow-m3-s]}]
                                 (and (finite? elapsed-ms) (not (neg? elapsed-ms))
                                      (finite? flow-m3-s) (not (neg? flow-m3-s)))) flows))))
         "Expected bounded camera samples and a finite held-flow history")
  (let [obs (optical-observations samples path-m)
        flows (filterv #(<= (:elapsed-ms %) (:elapsed-ms (peek obs))) flows)
        tail (tail-fit obs)
        metered? (some #(pos? (:flow-m3-s %)) flows)
        result
        (if-not metered? tail
          (let [timeline (schedule obs flows)
                levels (mapv :density obs)
                average (/ (reduce + levels) (count levels))
                variance (reduce + (map #(let [x (- % average)] (* x x)) levels))
                search (fn [half-lives mix-times]
                         (apply max-key :r-squared
                                (for [h half-lives m mix-times
                                      :let [a (fit-rates timeline volume-m3 h m variance)] :when a] a)))
                h (:clearance-half-life-s tail)
                coarse (search (map #(* h %) [0.25 0.4 0.65 1 1.5 2.25 4])
                               [0.125 0.25 0.5 1 2 4 8 16 32 64 128 256])
                fine (reduce (fn [best scale]
                               (let [near (fn [x] (map #(* x (Math/pow scale %)) [-2 -1 0 1 2]))]
                                 (search (near (:clearance-half-life-s best)) (near (:mixing-seconds best)))))
                             coarse [1.25 1.10 1.04 1.015])]
            (check (and (> (:r-squared fine) 0.88) (<= 0.001 (:extinction-per-m fine) 1000))
                   "Fog levels do not match the metered burst; check other sources and the sightline")
            fine))]
    (assoc result :samples (count obs) :reference-path-m (double path-m)
           :method (if metered? :metered-burst :clearance-tail))))

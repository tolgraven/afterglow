(ns afterglow.render.atmosphere.calibration
  "Fit a stationary sightline from linear camera contrast and held nozzle flows.
  Optical depth is dimensionless. The fit uses metres, seconds and cubic metres."
  (:require [afterglow.render.atmosphere :as fog]))

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

(defn- log-decay [samples]
  (let [xs (mapv #(/ (:elapsed-ms %) 1000.0) samples)
        ys (mapv #(Math/log (:density %)) samples)
        mean #(/ (reduce + 0.0 %) (count %))
        mx (mean xs) my (mean ys)
        dx (mapv #(- % mx) xs) dy (mapv #(- % my) ys)
        slope (/ (reduce + (map * dx dy)) (reduce + (map * dx dx)))
        residual (reduce + (map (fn [x y] (let [d (- y (* slope x))] (* d d))) dx dy))]
    {:slope slope :r-squared (- 1.0 (/ residual (reduce + (map * dy dy))))}))

(defn- tail-fit [observations metered?]
  (let [clearing (filterv #(= :clearing (:phase %)) observations)
        peak (apply max-key :density clearing)
        tail (filterv #(and (>= (:elapsed-ms %) (:elapsed-ms peak))
                            (> (:density %) (* 0.05 (:density peak)))) clearing)]
    (check (and (>= (count tail) 5) (>= (- (:elapsed-ms (peek tail)) (:elapsed-ms peak)) 3000)
                (> (:density peak) 0.003)
                (< (:density (peek tail)) (* 0.78 (:density peak))))
           "Keep scanning until the mixed fog has clearly fallen from its peak")
    ;; A metered search models the plume separately and only needs an initial
    ;; clearance estimate. Without a meter, use the latter half of the observed
    ;; decay in time and require its two halves to agree on the decay rate.
    (let [mid-time (fn [xs] (* 0.5 (+ (:elapsed-ms (first xs)) (:elapsed-ms (peek xs)))))
          settled (if metered? tail (filterv #(>= (:elapsed-ms %) (mid-time tail)) tail))]
      (when-not metered?
        (let [mid (mid-time settled)
              early (filterv #(<= (:elapsed-ms %) mid) settled)
              late (filterv #(>= (:elapsed-ms %) mid) settled)]
          (check (and (>= (count early) 3) (>= (count late) 3)
                      (>= (- (:elapsed-ms (peek settled)) (:elapsed-ms (first settled))) 3000)
                      (< (:density (peek settled)) (* 0.78 (:density (first settled))))
                      (let [a (:slope (log-decay early)) b (:slope (log-decay late))]
                        (and (neg? a) (neg? b) (<= (abs (- a b)) (* 0.05 (min (- a) (- b)))))))
                 "Continue scanning until the plume is mixed and the late clearance rate is steady")))
      (let [{:keys [slope r-squared]} (log-decay settled)
            half-life (/ (- (Math/log 2.0)) slope)]
        (check (and (finite? half-life) (<= 0.1 half-life 86400) (> r-squared 0.75))
               "Clearing does not follow a steady decay; check the sightline and repeat")
        {:clearance-half-life-s half-life :r-squared r-squared}))))

(defn- schedule [observations flows]
  (let [events (reduce (fn [m {:keys [elapsed-ms density]}] (assoc-in m [elapsed-ms :reading] density))
                       (sorted-map) observations)
        events (reduce (fn [m {:keys [elapsed-ms flow-m3-s]}] (assoc-in m [elapsed-ms :flow] flow-m3-s))
                       events flows)]
    (let [n (count events)
          intervals (double-array n)
          rates (double-array n)
          readings (double-array n)]
      ;; Compile the immutable observation times once. Each search candidate
      ;; reads these same primitive arrays without allocating per sample.
      (loop [pairs (seq events) i 0 prior-ms 0.0 held-rate 0.0]
        (if-let [[ms {:keys [reading flow]}] (first pairs)]
          (do (aset intervals i (/ (- (double ms) prior-ms) 1000.0))
              (aset rates i held-rate)
              (aset readings i (double (or reading Double/NaN)))
              (recur (next pairs) (inc i) (double ms) (double (or flow held-rate))))
          {:intervals intervals :rates rates :readings readings})))))

(defn- fit-rates [{:keys [intervals rates readings]} volume half-life mixing total-variance]
  ;; The room and nozzle use the same physical response as the live solver.
  (let [^doubles intervals intervals ^doubles rates rates ^doubles readings readings
        k (/ (Math/log 2) (double half-life)) km (+ k (/ 1.0 (double mixing)))
        volume (double volume)]
    (loop [i 0 total 0.0 local 0.0 xx 0.0 xy 0.0 yy 0.0]
      (if (= i (alength intervals))
        (when (pos? xx)
          (let [coefficient (/ xy xx)
                rss (max 0.0 (- yy (* xy coefficient)))]
            {:extinction-per-m coefficient :mixing-seconds mixing :clearance-half-life-s half-life
             :r-squared (- 1.0 (/ rss total-variance))}))
        (let [dt (aget intervals i) q (aget rates i) reading (aget readings i)
              total (fog/held-volume total q k dt)
              local (fog/held-volume local q km dt)
              x (/ (- total local) volume)]
          (if (Double/isNaN reading)
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
        metered? (some #(pos? (:flow-m3-s %)) flows)
        tail (tail-fit obs metered?)
        result
        (if-not metered? tail
          (let [timeline (schedule obs flows)
                levels (mapv :density obs)
                average (/ (reduce + levels) (count levels))
                variance (reduce + (map #(let [x (- % average)] (* x x)) levels))
                search (fn [half-lives mix-times]
                         (apply max-key :r-squared
                                (for [h half-lives m mix-times
                                      :when (and (<= 0.1 h 86400) (<= 0.001 m 86400))
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

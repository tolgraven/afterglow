(ns afterglow.runtime.keyframes.values
  "Interpolate uncomposited effect outputs. Arrays are read-only endpoints.
  Each interpolated numeric column has its own storage."
  (:require [afterglow.render.photometry :as photometry]
            [afterglow.runtime :as runtime]
            [afterglow.time :as time]))

(def emitters (into #{:dimmer :color} (keys photometry/emitter-spectrum)))
(def geometry #{:aim :direction})
(def continuous (into (into emitters geometry) [:pan :tilt :zoom :focus :beat-ratio]))

(defn- invalid! [reason] (throw (ex-info reason {:type ::invalid-sampler})))

(defn- bounds [attr hdr?]
  (cond
    (or (geometry attr) (= :beat-ratio attr)) [Double/NEGATIVE_INFINITY Double/POSITIVE_INFINITY]
    (and hdr? (emitters attr)) [0.0 Double/POSITIVE_INFINITY]
    :else [0.0 1.0]))

(defn- valid-value? [attr value hdr?]
  (let [[lo hi] (bounds attr hdr?)
        valid? (fn [x] (and (time/finite-number? x) (<= lo x hi)))]
    (if (or (= attr :color) (geometry attr))
      (and (vector? value) (= 3 (count value)) (every? valid? value))
      (valid? value))))

(defn- valid-column? [attr ^doubles xs hdr?]
  (let [[lo hi] (bounds attr hdr?) lo (double lo) hi (double hi)]
    (loop [i 0]
      (or (= i (alength xs))
          (let [x (aget xs i)]
            (and (Double/isFinite x) (<= lo x hi) (recur (inc i))))))))

(defn- valid-opacity? [x]
  (or (nil? x) (and (time/finite-number? x) (<= 0 x 1))))

(defn- only-keys? [allowed data] (and (map? data) (every? allowed (keys data))))

(defn- validate-block! [hdr? {:keys [kind assignments batch] :as block}]
  (let [target-id? #(or (keyword? %) (string? %))
        blends #{:replace :add :max}
        valid-row? (fn [{:keys [target-id attribute value blend opacity] :as row}]
                     (and (only-keys? #{:target-id :attribute :value :blend :opacity} row)
                          (target-id? target-id) (continuous attribute) (valid-opacity? opacity)
                          (or (nil? blend) (and (blends blend) (or (not (geometry attribute)) (= blend :replace)))) (valid-value? attribute value hdr?)))]
    (case kind
      :assignments (when-not (and (= #{:kind :assignments} (set (keys block)))
                                  (vector? assignments) (every? valid-row? assignments)) (invalid! "Invalid predictive endpoint"))
      :batch (let [{:keys [target-ids count outputs blend]} batch n (clojure.core/count target-ids)]
               (when-not (and (= #{:kind :batch} (set (keys block)))
                              (only-keys? #{:target-ids :outputs :count :blend :opacity} batch) (valid-opacity? (:opacity batch))
                              (vector? target-ids) (every? target-id? target-ids)
                              (or (nil? count) (= count n)) (map? outputs) (seq outputs)
                              (or (nil? blend) (blends blend))
                              (every? (fn [[attr {:keys [components type values] :as field}]]
                                        (let [vec3? (or (= attr :color) (geometry attr))]
                                          (and (only-keys? #{:type :values :components} field) (continuous attr) (= components (if vec3? 3 1))
                                               (= type (if vec3? :vec3 :number)) (instance? double/1 values)
                                               (= (alength ^doubles values) (* n components))
                                               (valid-column? attr values hdr?))))
                                      outputs))
                 (invalid! "Invalid predictive endpoint")))
      (invalid! "Invalid predictive endpoint"))))

(defn validate-blocks! [blocks hdr?]
  (when-not (vector? blocks) (invalid! "Expected ordered predictive blocks"))
  (run! (partial validate-block! hdr?) blocks)
  blocks)

(defn blocks [context result]
  (when-not (and (= (:state context) (:state result)) (= [] (:intents result))
                 (false? (:done? result)) (vector? (:assignments result)))
    (invalid! "A predictive sampler must only produce continuous native outputs"))
  (let [fields (validate-blocks! (:contributions (runtime/append-contributions result [])) (get-in context [:frame :hdr?]))
        reader (::runtime/observe (meta result))]
    (with-meta fields (cond-> {::sample-clock (time/frame-clock (:frame context))}
                        reader (assoc ::runtime/observe reader)))))

(defn- scalar [a b t lo hi]
  (let [v (+ (double a) (* (double t) (- (double b) (double a))))]
    (max lo (min hi v))))

(defn- assignment [t hdr? a b]
  (when-not (= (dissoc a :value) (dissoc b :value))
    (invalid! "Predictive assignment topology changed within a keyframe"))
  (let [[lo hi] (bounds (:attribute a) hdr?) a-value (:value a) b-value (:value b)
        sample #(scalar %1 %2 t lo hi)]
    (assoc a :value (if (and (vector? a-value) (vector? b-value) (= (count a-value) (count b-value)))
                      (mapv sample a-value b-value)
                      (sample a-value b-value)))))

(defn- column [attr t hdr? from to]
  (when-not (= (dissoc from :values) (dissoc to :values))
    (invalid! "Predictive column shape changed within a keyframe"))
  (let [^doubles a (:values from) ^doubles b (:values to) n (alength a)
        t (double t) [lo hi] (bounds attr hdr?) lo (double lo) hi (double hi)
        out (double-array n)]
    (when-not (= n (alength b)) (invalid! "Predictive field size changed"))
    (dotimes [i n]
      (let [x (aget a i)]
        (aset-double out i (max lo (min hi (+ x (* t (- (aget b i) x))))))))
    (assoc from :values out)))

(defn- blend-block [t hdr? a b]
  (when-not (= (:kind a) (:kind b))
    (invalid! "Predictive output representation changed within a keyframe"))
  (case (:kind a)
    :assignments
    (let [as (:assignments a) bs (:assignments b)]
      (when-not (= (count as) (count bs)) (invalid! "Predictive assignment count changed"))
      (assoc a :assignments (mapv (partial assignment t hdr?) as bs)))
    :batch
    (let [left (:batch a) right (:batch b)
          as (:outputs left) bs (:outputs right)]
      (when-not (and (= (dissoc left :outputs) (dissoc right :outputs)) (= (set (keys as)) (set (keys bs))))
        (invalid! "Predictive batch topology changed within a keyframe"))
      (assoc-in a [:batch :outputs] (reduce-kv (fn [m attr field] (assoc m attr (column attr t hdr? field (bs attr)))) {} as)))))

(defn blend [origin target t hdr?]
  (cond
    (zero? t) origin
    (== 1.0 t) target
    :else (do (when-not (= (count origin) (count target)) (invalid! "Predictive block count changed"))
              (mapv (partial blend-block t hdr?) origin target))))

(defn map-columns [f blocks]
  (mapv (fn [block]
          (if (= :batch (:kind block))
            (update-in block [:batch :outputs] update-vals #(update % :values f))
            block)) blocks))

(defn- batch-rows [{:keys [target-ids blend outputs opacity]}]
  (for [[i id] (map-indexed vector target-ids)
        [attr {:keys [components values]}] outputs]
    (let [^doubles xs values start (* i components)]
      (cond-> {:target-id id :attribute attr :blend (or blend :replace)
               :value (if (= 1 components) (aget xs start)
                         (mapv #(aget xs (+ start %)) (range components)))}
        (some? opacity) (assoc :opacity opacity)))))

(defn- rows [blocks]
  (into [] (mapcat (fn [block] (if (= :batch (:kind block))
                                 (batch-rows (:batch block)) (:assignments block)))) blocks))

(defn- align [order other]
  ;; Different IR paths can group the same assignments differently. Preserve
  ;; the origin's order and the order of successive writes to one attribute.
  (let [key-of (juxt :target-id :attribute)
        index (group-by key-of other)]
    (loop [remaining order index index result (transient [])]
      (if-let [row (first remaining)]
        (let [k (key-of row) available (get index k)]
          (when-not (seq available) (invalid! "Predictive effect changed its targets"))
          (recur (next remaining) (assoc index k (next available)) (conj! result (first available))))
        (do (when (some seq (vals index)) (invalid! "Predictive effect added targets"))
            (persistent! result))))))

(defn- same-columns? [left right]
  (and (= (set (keys left)) (set (keys right)))
       (every? (fn [[attribute a]]
                 (let [b (right attribute)]
                   (and (= (dissoc a :values) (dissoc b :values))
                        (= (alength ^doubles (:values a)) (alength ^doubles (:values b)))))) left)))

(defn- same-layout? [a b]
  (and (= (:kind a) (:kind b))
       (case (:kind a)
         :assignments (let [left (:assignments a) right (:assignments b)]
                        (and (= (count left) (count right))
                             (every? true? (map #(= (dissoc %1 :value) (dissoc %2 :value)) left right))))
         :batch (let [left (:batch a) right (:batch b)]
                  (and (= (dissoc left :outputs) (dissoc right :outputs))
                       (same-columns? (:outputs left) (:outputs right)))))))

(defn- align-endpoints [origin target]
  (if (and (= (count origin) (count target)) (every? true? (map same-layout? origin target)))
    [origin target]
    (let [start (rows origin)
          end (align start (rows target))]
      (when-not (every? true? (map #(= (dissoc %1 :value) (dissoc %2 :value)) start end))
        (invalid! "Predictive effect changed its assignment properties"))
      [(with-meta [{:kind :assignments :assignments start}] (meta origin))
       (with-meta [{:kind :assignments :assignments end}] (meta target))])))

(defn- geometry-block? [{:keys [kind assignments batch]}]
  (case kind
    :batch (some geometry (keys (:outputs batch)))
    :assignments (some (comp geometry :attribute) assignments)))

(defn- can-overshoot? [curve]
  (let [shape (if (map? curve) (:type curve) curve)]
    (or (= shape :spring)
        (and (= shape :cubic-bezier)
             (some #(not (<= 0 % 1)) (map (:points curve) [1 3]))))))

(defn- check-chord! [overshoot? ax ay az bx by bz]
  (let [ax (double ax) ay (double ay) az (double az)
        bx (double bx) by (double by) bz (double bz)
        m (Math/sqrt (+ (* ax ax) (* ay ay) (* az az)))
        n (Math/sqrt (+ (* bx bx) (* by by) (* bz bz)))]
    (when-not (and (Double/isFinite m) (Double/isFinite n) (pos? m) (pos? n))
      (invalid! "Aim or direction reaches zero distance"))
    (let [cosine (+ (* (/ ax m) (/ bx n)) (* (/ ay m) (/ by n)) (* (/ az m) (/ bz n)))]
      ;; Interpolating through the emitter loses the direction of the real curve.
      (when (or (< cosine -0.999999999999)
                (and overshoot? (> cosine 0.999999999999) (not (== m n))))
        (invalid! "Use live movement samples along a singular aim or direction chord")))))

(defn- position-for [positions attribute target-id]
  (if (= :aim attribute) (get positions target-id [0 0 0]) [0 0 0]))

(defn- check-assignments! [overshoot? positions left right]
  (doseq [[a b] (map vector left right)
          :let [attr (:attribute a)]
          :when (geometry attr)]
    (let [[x y z] (position-for (when (= :aim attr) (force positions)) attr (:target-id a))
          [ax ay az] (:value a) [bx by bz] (:value b)]
      (check-chord! overshoot? (- ax x) (- ay y) (- az z) (- bx x) (- by y) (- bz z)))))

(defn- check-batch! [overshoot? positions left right]
  (doseq [attr geometry
          :let [^doubles from (get-in left [:outputs attr :values])]
          :when from]
    (let [^doubles to (get-in right [:outputs attr :values])
          ids (:target-ids left)
          positions (when (= :aim attr) (force positions))]
      (dotimes [i (count ids)]
        (let [[x y z] (position-for positions attr (nth ids i))
              x (double x) y (double y) z (double z)
              ix (* 3 i) iy (inc ix) iz (inc iy)]
          (check-chord! overshoot?
                        (- (aget from ix) x) (- (aget from iy) y) (- (aget from iz) z)
                        (- (aget to ix) x) (- (aget to iy) y) (- (aget to iz) z)))))))

(defn fixture-positions [fixtures]
  (into {} (map (juxt :id #(or (:position %) [0 0 0]))) fixtures))

(defn indexed-endpoints
  "Check aligned geometry against the frozen rig. Direction chords are already
  emitter-relative. Only absolute aim needs to realize the shared lookup."
  [origin target positions curve]
  (let [[origin target :as aligned] (align-endpoints origin target)]
    (when (some geometry-block? origin)
      (let [overshoot? (can-overshoot? curve)]
        (doseq [[left right] (map vector origin target)]
          (case (:kind left)
            :batch (check-batch! overshoot? positions (:batch left) (:batch right))
            :assignments (check-assignments! overshoot? positions (:assignments left) (:assignments right))))))
    aligned))

(defn endpoints [origin target fixtures curve]
  (indexed-endpoints origin target (delay (fixture-positions fixtures)) curve))

(defn read-values [blocks target attribute]
  (let [relevant? (fn [row] (and (= target (:target-id row)) (= attribute (:attribute row))))
        values-of (fn [{:keys [kind batch assignments]}]
                    (if (= :assignments kind)
                      (into [] (comp (filter relevant?) (map :value)) assignments)
                      (let [{:keys [target-ids outputs]} batch
                            {:keys [components values]} (get outputs attribute)
                            i (if values (.indexOf ^java.util.List target-ids target) -1)]
                        (when-not (neg? i)
                          (let [^doubles xs values start (* i components)]
                            [(if (= components 1) (aget xs start)
                               (mapv #(aget xs (+ start %)) (range components)))])))))]
    (into [] (mapcat values-of) blocks)))

(ns afterglow.spatial.trace
  "Trace a segment through the local geometry carried by a moving ball.
  Each interval is expressed as a fraction of the body's linear substep."
  (:require [afterglow.spatial.shape :as shape]))

(defn- clip [span p step lo hi]
  (when span
    (if (zero? step)
      (when (<= lo p hi) span)
      (let [a (/ (- lo p) step) b (/ (- hi p) step)
            start (max (first span) (min a b)) end (min (second span) (max a b))]
        (when (<= start end) [start end])))))

(defn- clip-box [bounds origin direction]
  (reduce (fn [span [p d lo hi]] (or (clip span p d lo hi) (reduced nil)))
          [0.0 1.0] (map vector origin direction (:min bounds) (:max bounds))))

(defn- at [point delta t] (mapv (fn [p d] (+ p (* t d))) point delta))

(defn- entering [distance outside inside]
  (loop [lo outside hi inside n 0]
    (if (= n 33) hi
      (let [mid (* 0.5 (+ lo hi))]
        (if (pos? (distance mid))
          (recur mid hi (inc n))
          (recur lo mid (inc n)))))))

(defn- interior [distance start end]
  ;; A convex primitive has a convex distance along a line. Find an interior
  ;; witness for clipped diagonals and thin shapes even when both ends are out.
  (loop [a start b end n 0]
    (let [mid (* 0.5 (+ a b))]
      (cond (<= (distance mid) 0.0) mid
            (= n 50) nil
            :else (let [u (/ (+ a a b) 3.0) v (/ (+ a b b) 3.0)]
                    (if (< (distance u) (distance v))
                      (recur a v (inc n)) (recur u b (inc n))))))))

(defn- convex [spec {:keys [distance bounds]} point delta]
  (when-let [[a b] (if bounds (clip-box bounds point delta) [0.0 1.0])]
    (if (or (= :box (:shape spec)) (and (= :rounded-box (:shape spec)) (zero? (:rounding spec 0))))
      [[a b]]
      (let [d #(distance (at point delta %))
            a? (<= (d a) 0.0) b? (<= (d b) 0.0)
            witness (cond a? a b? b :else (interior d a b))]
        (when (some? witness)
          [[(if a? a (entering d a witness)) (if b? b (entering d b witness))]])))))

(defn- join [spans [a b]]
  (if (= a (second (peek spans)))
    (conj (pop spans) [(first (peek spans)) b])
    (conj spans [a b])))

(defn- boolean-trace [traces inside? point delta]
  (let [cuts (into (sorted-set 0.0 1.0) (comp (mapcat #(% point delta)) cat) traces)
        included? (fn [[a b]] (inside? (at point delta (* 0.5 (+ a b)))))
        intervals (filter included? (partition 2 1 cuts))
        ;; Retain an isolated tangent contact as a zero-duration interval.
        touches (for [t cuts :when (and (inside? (at point delta t))
                                        (not-any? (fn [[a b]] (<= a t b)) intervals))]
                  [t t])]
    (reduce join [] (sort-by first (concat intervals touches)))))

(defn prepare
  "Compile geometry once before stepping the body. Call :intervals with the
  initial local point and its displacement relative to the moving body."
  [{:keys [parts translation] :as spec}]
  (let [local (dissoc spec :translation :scale)
        plan (shape/prepare local)
        trace (cond
                (and (= :ball (:shape local)) (:geometry local))
                (let [child (:intervals (prepare (:geometry local)))]
                  (fn [p d] (child (mapv - p (:position local)) d)))
                (#{:union :intersection :difference} (:shape local))
                (partial boolean-trace (mapv (comp :intervals prepare) parts) (:inside? plan))
                :else (partial convex local plan))
        {:keys [inverse inverse-delta]} (shape/coordinates spec (:bounds plan))]
    {:bounds (:bounds (shape/prepare spec))
     :intervals (if inverse (fn [point delta] (trace (inverse point) (inverse-delta delta))) trace)}))

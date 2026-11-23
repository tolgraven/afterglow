(ns afterglow.spatial.geometry
  "Portable venue shapes in metres. The X index prunes sphere and box queries
  before testing the full shape. A rig's prepared index stays outside show files."
  (:require [afterglow.spatial.shape :as field-shape]
            [afterglow.time :as time]))

(defn vec3? [v] (and (vector? v) (= 3 (count v)) (every? time/finite-number? v)))
(defn nonnegative? [x] (and (time/finite-number? x) (not (neg? x))))
(defn valid-id? [x] (or (keyword? x) (string? x)))
(defn invalid! [message value] (throw (ex-info message {:value value})))

(defn length3 [[x y z]]
  (Math/hypot (Math/hypot (double x) (double y)) (double z)))
(defn- dist2 [[ax ay az] [bx by bz]]
  (let [x (- (double ax) (double bx)) y (- (double ay) (double by)) z (- (double az) (double bz))]
    (+ (* x x) (* y y) (* z z))))

(defn box? [{:keys [min max]}]
  (and (vec3? min) (vec3? max) (every? true? (map < min max))))

(defn- shape-valid? [{:keys [shape position radius height parts planes] :as spec} depth]
  (and (< depth 16)
       (or (not (contains? spec :scale)) (and (vec3? (:scale spec)) (every? pos? (:scale spec))))
       (or (not (contains? spec :translation)) (vec3? (:translation spec)))
       (or (not (contains? spec :geometry))
           (and (= shape :ball) (not= :ball (:shape (:geometry spec))) (shape-valid? (:geometry spec) (inc depth))))
       (case shape
         :rounded-box (and (vec3? position) (vec3? (:size spec)) (every? pos? (:size spec))
                           (time/finite-number? (:rounding spec 0.0)) (<= 0 (:rounding spec 0.0) 1))
         (:sphere :ball) (and (vec3? position) (nonnegative? radius))
         :box (box? spec)
         :cylinder (and (vec3? position) (nonnegative? radius) (nonnegative? height))
         :polyhedron (and (vector? planes) (<= 1 (count planes) 128)
                          (every? (fn [{:keys [normal distance]}]
                                    (and (vec3? normal) (pos? (length3 normal)) (time/finite-number? distance))) planes))
         (:union :intersection :difference)
         (and (vector? parts) (<= 1 (count parts) 64)
              (every? #(and (not= :ball (:shape %)) (shape-valid? % (inc depth))) parts))
         false)))

(defn validate! [spec]
  (let [children (fn [v] (if-let [g (:geometry v)] [g] (:parts v)))
        nodes (tree-seq #(or (:geometry %) (:parts %)) children spec)]
    (when (> (bounded-count 1025 nodes) 1024)
      (invalid! "A sculpted volume can contain at most 1024 shape nodes" nil)))
  (when-not (shape-valid? spec 0) (invalid! "Invalid venue shape or nesting" spec))
  spec)

(defn inside?
  "A point on a primitive boundary belongs to it. A difference removes the
  subtracting shape's boundary as well as its interior."
  [spec point]
  ((:inside? (field-shape/prepare spec)) point))

(defrecord Rig [ids rows xs directional])

(defn prepare-rig [fixtures]
  (if (instance? Rig fixtures) fixtures
    (let [rows (->> fixtures
                    (map (fn [{:keys [id position] :or {position [0.0 0.0 0.0]}}]
                           (when-not (and (valid-id? id) (vec3? position))
                             (invalid! "Spatial fixture needs an ID and a finite position" [id position]))
                           [id position]))
                    (sort-by (comp first second)) vec)]
      (let [directional? (fn [{:keys [beam-angle channels direction]}]
                           (or beam-angle direction (:pan channels) (:tilt channels) (:red channels) (:white channels) (:dimmer channels)))]
        (->Rig (set (map first rows)) rows (double-array (map (comp first second) rows))
               (filterv directional? fixtures))))))

(defn- lower-bound [^doubles xs x]
  (loop [lo 0 hi (alength xs)]
    (if (= lo hi) lo
      (let [mid (unsigned-bit-shift-right (+ lo hi) 1)]
        (if (< (aget xs mid) x) (recur (inc mid) hi) (recur lo mid))))))

(defn candidates
  "Wire-identified fixture positions within a field's X bounds. A nil box is unbounded."
  [{:keys [rows xs]} bounds]
  (if-not bounds
    rows
    (let [lo (first (:min bounds)) hi (first (:max bounds))]
      (if (> lo hi) []
        (subvec rows (lower-bound xs (double lo)) (lower-bound xs (Math/nextUp (double hi))))))))

(defn fixtures-in [rig volume]
  (let [{:keys [inside? bounds]} (field-shape/prepare volume)]
    (into #{} (keep (fn [[id point]] (when (inside? point) id)))
          (candidates rig bounds))))

(defn sweep
  "Return [fixture-id entry exit still-inside?] for the segment swept by a
  sphere. Times are fractions of this substep. This catches a fast throw
  crossing a small fixture volume completely between two physical frames."
  [rig [x y z] [ex ey ez] radius]
  (let [x (double x) y (double y) z (double z)
        dx (- (double ex) x) dy (- (double ey) y) dz (- (double ez) z)
        rr (* (double radius) (double radius)) length2 (+ (* dx dx) (* dy dy) (* dz dz))
        ^doubles xs (:xs rig)
        end (+ (max x ex) radius)]
    (loop [i (int (lower-bound xs (- (min x ex) radius))) hits (transient [])]
      (if (or (= i (alength xs)) (> (aget xs i) end)) (persistent! hits)
        (let [[id [a b c]] (nth (:rows rig) i)
              ax (- (double a) x) ay (- (double b) y) az (- (double c) z)
              center (/ (+ (* ax dx) (* ay dy) (* az dz)) length2)
              cx (- ax (* center dx)) cy (- ay (* center dy)) cz (- az (* center dz))
              chord2 (- rr (+ (* cx cx) (* cy cy) (* cz cz)))
              half (if (neg? chord2) 0.0 (Math/sqrt (/ chord2 length2)))
              enter (max 0.0 (- center half)) leave (min 1.0 (+ center half))]
          (recur (inc i)
                 (if (and (>= chord2 0.0) (<= enter leave))
                   (conj! hits [id enter leave (<= (dist2 [a b c] [ex ey ez]) rr)])
                   hits)))))))

(defn sweep-geometry [rig {:keys [intervals bounds]} from to]
  (let [delta (mapv - from to)
        swept (when bounds {:min (mapv + (mapv min from to) (:min bounds))
                            :max (mapv + (mapv max from to) (:max bounds))})
        contacts (fn [[id p]]
                   (map (fn [[entry exit]] [id entry exit (== 1.0 exit)])
                        (intervals (mapv - p from) delta)))]
    (into [] (mapcat contacts) (candidates rig swept))))

(ns afterglow.spatial.geometry
  "Portable venue shapes in metres. The X index prunes sphere and box queries
  before testing the full shape. A rig's prepared index stays outside show files."
  (:require [afterglow.render.photometry :as photometry]
            [afterglow.render.shutter :as shutter]
            [afterglow.spatial.shape :as field-shape]
            [afterglow.time :as time]))

(defn vec3? [v]
  (and (vector? v) (= 3 (count v))
       (time/finite-number? (nth v 0))
       (time/finite-number? (nth v 1))
       (time/finite-number? (nth v 2))))

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

(def ^:private visible-emitters
  (into #{} (keep (fn [[attr [response _]]] (when (pos? response) attr))) photometry/emitter-spectrum))

(defn- optical-fixture [{:keys [channels beam-angle direction] :as fixture}]
  (when (or beam-angle direction (:pan channels) (:tilt channels) (:dimmer channels)
            (some visible-emitters (keys channels)))
    (cond-> fixture
      (or (:shutter channels) (:strobe channels)) (assoc ::shutters (shutter/profile channels)))))

(defn- position-columns [rows]
  ;; Publish the read-only columns in row rank order only after all coordinates qualify.
  (let [size (count rows)
        ^doubles ys (double-array size)
        ^doubles zs (double-array size)]
    (loop [i (int 0)]
      (if (= i size)
        [ys zs]
        (let [point (nth (nth rows i) 1)
              y (nth point 1)
              z (nth point 2)]
          (when (and (double? y) (double? z))
            (aset ys i (double y))
            (aset zs i (double z))
            (recur (unchecked-inc-int i))))))))

(defn prepare-rig [fixtures]
  (if (instance? Rig fixtures) fixtures
    (let [rows (->> fixtures
                    (map (fn [{:keys [id position] :or {position [0.0 0.0 0.0]}}]
                           (when-not (and (valid-id? id) (vec3? position))
                             (invalid! "Spatial fixture needs an ID and a finite position" [id position]))
                           [id position]))
                    (sort-by (comp first second)) vec)]
      (assoc (->Rig (set (map first rows)) rows (double-array (map (comp first second) rows))
                    (into [] (keep optical-fixture) fixtures))
             ::position-columns (delay (position-columns rows))))))

(defn- lower-bound [^doubles xs x]
  (loop [lo 0 hi (alength xs)]
    (if (= lo hi) lo
      (let [mid (unsigned-bit-shift-right (+ lo hi) 1)]
        (if (< (aget xs mid) x) (recur (inc mid) hi) (recur lo mid))))))

(defn- candidate-window [xs lo hi]
  (when-not (> lo hi)
    [(lower-bound xs (double lo)) (lower-bound xs (Math/nextUp (double hi)))]))

(defn candidates
  "Wire-identified fixture positions within a field's X bounds. A nil box is unbounded."
  [{:keys [rows xs]} bounds]
  (if-not bounds
    rows
    (if-let [[start end] (candidate-window xs (first (:min bounds)) (first (:max bounds)))]
      (subvec rows start end)
      [])))

(defn- finite-double-point? [point]
  (and (vector? point) (= 3 (count point))
       (every? #(and (double? %) (Double/isFinite (double %))) point)))

(defn- packed-box? [lo hi]
  (and (finite-double-point? lo) (finite-double-point? hi)
       (every? true? (map <= lo hi))))

(defn- reduce-packed-candidates [rf init rows [start end] [ys zs] lo hi]
  (let [^doubles ys ys ^doubles zs zs
        ymin (double (nth lo 1)) ymax (double (nth hi 1))
        zmin (double (nth lo 2)) zmax (double (nth hi 2))
        end (int end)]
    (loop [i (int start), result init]
      (if (= i end)
        result
        (let [y (aget ys i) z (aget zs i)]
          (if (or (< y ymin) (> y ymax) (< z zmin) (> z zmax))
            (recur (unchecked-inc-int i) result)
            (let [result (rf result (nth rows i))]
              (if (reduced? result)
                @result
                (recur (unchecked-inc-int i) result)))))))))

(defn reduce-box-candidates
  "Reduce admitted position rows in the rig's existing X rank order. The X
  window uses index coordinates, and Y/Z compare the original positions."
  [{:keys [rows xs] :as rig} {lo :min hi :max :as bounds} rf init]
  (if-let [columns (when (packed-box? lo hi) (some-> (::position-columns rig) deref))]
    (reduce-packed-candidates rf init rows (candidate-window xs (first lo) (first hi)) columns lo hi)
    (let [[_ ymin zmin] lo [_ ymax zmax] hi
          admit (fn [result [_ [_ y z] :as row]]
                  (if (and bounds (or (< y ymin) (> y ymax) (< z zmin) (> z zmax)))
                    result
                    (rf result row)))]
      (reduce admit init (candidates rig bounds)))))

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

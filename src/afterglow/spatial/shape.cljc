(ns afterglow.spatial.shape
  "Compile a venue shape in metres to a signed-distance function and a bounding box.
  A negative distance is inside. Boolean combinations use min/max distance fields."
  (:require #?(:clj [clojure.math :as math] :cljs [cljs.math :as math])))

(defn- box [lo hi] {:min lo :max hi})
(defn- centered-box [p half] (box (mapv - p half) (mapv + p half)))
(defn- centered-radius [p radius] (centered-box p [radius radius radius]))
(defn- length [x y z] (math/hypot (math/hypot x y) z))

(defn- sphere [{[cx cy cz :as p] :position r :radius}]
  {:witnesses [{:center p :radius r}] :bounds (centered-radius p r)
   :distance (fn [[x y z]] (- (length (- x cx) (- y cy) (- z cz)) r))})

(defn- rounded-box [[cx cy cz :as center] [hx hy hz :as half-size] r]
  (let [bx (- hx r) by (- hy r) bz (- hz r)]
    {:bounds (centered-box center half-size)
     :distance (fn [[x y z]]
                 (let [qx (- (abs (- x cx)) bx)
                       qy (- (abs (- y cy)) by)
                       qz (- (abs (- z cz)) bz)]
                   (+ (length (max 0.0 qx) (max 0.0 qy) (max 0.0 qz))
                      (min 0.0 (max qx qy qz)) (- r))))}))

(defn- cylinder [{[cx cy cz :as p] :position r :radius h :height}]
  (let [half (* 0.5 h)]
    {:bounds (centered-box p [r half r])
     :distance (fn [[x y z]]
                 (let [radial (- (math/hypot (- x cx) (- z cz)) r)
                       vertical (- (abs (- y cy)) half)]
                   (+ (math/hypot (max radial 0.0) (max vertical 0.0))
                      (min (max radial vertical) 0.0))))}))

(defn- half-space [{[x y z] :normal offset :distance}]
  (let [size (length x y z)]
    (fn [[px py pz]] (/ (- (+ (* x px) (* y py) (* z pz)) offset) size))))

(defn- extrema [op readers]
  (let [[read-point & others] readers]
    (fn [point] (reduce (fn [value read-other] (op value (read-other point))) (read-point point) others))))

(defn- merge-bounds [lo hi a b]
  (box (mapv lo (:min a) (:min b)) (mapv hi (:max a) (:max b))))

(defn- compound [op children]
  (let [distances (mapv :distance children)
        boxes (mapv :bounds children)
        contains-point? (mapv :inside? children)]
    (assoc (case op
      :union {:inside? (fn [p] (boolean (some #(% p) contains-point?)))
              :distance (extrema min distances)
              :bounds (when (every? some? boxes) (reduce (partial merge-bounds min max) boxes))}
      :intersection {:inside? (fn [p] (every? #(% p) contains-point?))
                     :distance (extrema max distances)
                     :bounds (when-let [finite (seq (remove nil? boxes))]
                               (reduce (partial merge-bounds max min) finite))}
      :difference {:inside? (fn [p] (and ((first contains-point?) p) (not-any? #(% p) (rest contains-point?))))
                   :distance (extrema max (into [(first distances)] (map #(comp - %)) (rest distances)))
                   :bounds (first boxes)})
           :witnesses (let [children (if (= op :difference) (take 1 children) children)
                            ws (vec (mapcat :witnesses children))
                            n (count ws)]
                        (if (<= n 64) ws
                          (mapv #(nth ws (quot (* % (dec n)) 63)) (range 64)))))))

(defn center [bounds]
  (when bounds (mapv #(+ (* 0.5 %1) (* 0.5 %2)) (:min bounds) (:max bounds))))

(defn coordinates
  "Local-to-world transform and its inverse. Scale about the chosen pivot
  before moving the shape. Used by both contact tracing and field sampling."
  [{:keys [scale translation position]} bounds]
  (when (or scale translation)
    (let [s (or scale [1.0 1.0 1.0])
          pivot (or position (center bounds) [0.0 0.0 0.0])
          offset (mapv (fn [p k t] (+ t (* p (- 1.0 k)))) pivot s (or translation [0.0 0.0 0.0]))]
      {:forward (fn [p] (mapv (fn [x k t] (+ (* x k) t)) p s offset))
       :inverse (fn [p] (mapv (fn [x k t] (/ (- x t) k)) p s offset))
       :inverse-delta (fn [d] (mapv / d s))
       :min-scale (reduce min s)})))

(defn- transformed [{:keys [distance inside? bounds witnesses] :as plan} transform]
  (if-not transform plan
    (let [{:keys [forward inverse min-scale]} transform
          move-witness (fn [w]
                         (if (map? w)
                           (-> w (update :center forward) (update :radius * min-scale))
                           (forward w)))]
      {:inside? (comp inside? inverse)
       :distance (fn [p] (* min-scale (distance (inverse p))))
       :bounds (when bounds (update-vals bounds forward))
       :witnesses (mapv move-witness witnesses)})))

(defn prepare
  "Compile a validated spatial shape. :translation offsets any shape and its children.
  A ball may carry a :geometry expressed in coordinates relative to its physical centre."
  [{:keys [shape position radius geometry parts size rounding translation planes] :as spec}]
  (let [plan (case shape
               :ball (if geometry (transformed (prepare geometry) (coordinates {:translation position} nil)) (sphere spec))
               :sphere (sphere spec)
               :box (let [lo (:min spec) hi (:max spec)]
                      (rounded-box (mapv #(* 0.5 (+ %1 %2)) lo hi) (mapv #(* 0.5 (- %2 %1)) lo hi) 0.0))
               :rounded-box (let [half-size (mapv #(* 0.5 %) size)]
                              (rounded-box position half-size (* (or rounding 0.0) (reduce min half-size))))
               :cylinder (cylinder spec)
               :polyhedron {:distance (extrema max (mapv half-space planes)) :bounds nil}
               (:union :intersection :difference) (compound shape (mapv prepare parts)))]
    (transformed (cond-> plan
                   (nil? (:inside? plan)) (assoc :inside? (fn [p] (<= ((:distance plan) p) 0.0)))
                   (nil? (:witnesses plan)) (assoc :witnesses (if-let [p (center (:bounds plan))] [p] [])))
                 (coordinates spec (:bounds plan)))))

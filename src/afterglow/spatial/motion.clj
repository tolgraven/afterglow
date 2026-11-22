(ns afterglow.spatial.motion
  "Deterministic semi-implicit integration for venue balls. Each fixed substep
  samples all gravitational sources at the same instant, moves the bodies, then
  resolves pair contacts in stable ID order."
  (:require [afterglow.spatial.geometry :as g]))

(def zero3 [0.0 0.0 0.0])
(def step-ms 5)
(def max-steps 80)
(defn- plus [a b] (mapv + a b))
(defn- minus [a b] (mapv - a b))
(defn- times [a n] (mapv #(* (double %) (double n)) a))
(defn- dot [a b] (reduce + (map * a b)))
(defn- clamp [lo x hi] (min hi (max lo x)))

(defn validate! [{:keys [bounds]} {:keys [radius velocity gravity angular-velocity rotation
                                           restitution hardness mass fixed? attraction throw-id] :as ball}]
  (when-not (and (pos? radius) (every? #(>= % (* 2.0 radius)) (map - (:max bounds) (:min bounds)))
                 (every? #(or (nil? %) (g/vec3? %)) [velocity gravity angular-velocity rotation])
                 (every? #(or (nil? %) (and (g/nonnegative? %) (<= % 1))) [restitution hardness])
                 (or (nil? attraction) (g/nonnegative? attraction))
                 (or (nil? mass) (and (g/nonnegative? mass) (pos? mass)))
                 (or (nil? fixed?) (boolean? fixed?))
                 (or (nil? throw-id) (g/valid-id? throw-id) (integer? throw-id)))
    (g/invalid! "Invalid ball size or dynamics" ball)))

(defn- constrain [bounds radius position]
  (mapv (fn [lo x hi] (clamp (+ lo radius) x (- hi radius)))
        (:min bounds) position (:max bounds)))

(defn body [old bounds spec]
  (let [launch (select-keys spec [:position :velocity :rotation :throw-id])
        prior (if (= launch (:launch old)) old
                {:launch launch :position (:position spec) :velocity (get spec :velocity zero3)
                 :rotation (get spec :rotation zero3) :deformation 0.0})]
    (-> prior
        (update :position #(constrain bounds (:radius spec) %))
        (cond-> (:fixed? spec) (assoc :velocity zero3)))))

(defn- accelerations [ids specs bodies gravity]
  (let [attractors (filterv #(pos? (:attraction (specs %) 0)) ids)]
    (into {}
          (for [id ids :let [p (:position (bodies id))]]
            [id (reduce (fn [a other]
                          (if (= id other) a
                            (let [offset (minus (:position (bodies other)) p)
                                  soft (max 0.001 (* 0.25 (+ (:radius (specs id)) (:radius (specs other)))))
                                  d (Math/sqrt (+ (dot offset offset) (* soft soft)))]
                              (plus a (times offset (/ (:attraction (specs other)) (* d d d)))))))
                        (:gravity (specs id) gravity) attractors)]))))

(defn- move-axis [x v lo hi seconds elasticity gravity]
  (if (= lo hi) [lo 0.0 []]
    (loop [x (double x) v (double v) left seconds impacts []]
      (let [wall (if (pos? v) hi lo)
            until (if (zero? v) Double/POSITIVE_INFINITY (/ (- wall x) v))]
        (cond
          (> until left) [(+ x (* left v)) v impacts]
          ;; Constant acceleration into a supporting surface produces a resting
          ;; contact. Other collisions report incoming normal speed before bounce.
          (and (zero? until) (<= (abs v) (+ 1.0e-9 (* (abs (double gravity)) seconds))))
          [wall 0.0 impacts]
          :else
          (let [reflected (* (- v) elasticity)
                hits (conj impacts {:side (if (pos? v) :max :min)
                                    :offset (- seconds (- left until)) :impact-speed (abs v)})]
            (if (or (zero? reflected) (>= (count hits) 8)) [wall 0.0 hits]
              (recur (double wall) reflected (- left until) hits))))))))

(defn- squash [speed hardness]
  (* (- 1.0 hardness) (/ speed (+ speed 2.0))))

(defn- move-body [id spec body acceleration bounds start]
  (let [seconds (/ step-ms 1000.0)
        r (:radius spec)
        position (:position body)
        elasticity (:restitution spec 0.85)
        hardness (:hardness spec 0.75)
        velocity (if (:fixed? spec) zero3 (plus (:velocity body) (times acceleration seconds)))
        axes (mapv (fn [i]
                     (move-axis (position i) (velocity i) (+ (get-in bounds [:min i]) r)
                                (- (get-in bounds [:max i]) r) seconds elasticity (acceleration i))) (range 3))
        events (into [] (mapcat (fn [i [_ _ hits]]
                                  (map (fn [{:keys [side offset impact-speed]}]
                                         {:type :spatial/bounce :volume-id id :time-ms (+ start (* 1000.0 offset))
                                          :surface [(nth [:x :y :z] i) side]
                                          :impact-speed impact-speed :deformation (squash impact-speed hardness)}) hits))
                                (range 3) axes))
        decay (* (:deformation body) (Math/exp (* -14.0 seconds)))]
    [(assoc body :position (mapv first axes) :velocity (mapv second axes)
            :rotation (plus (:rotation body) (times (:angular-velocity spec zero3) seconds))
            :deformation (reduce max decay (map :deformation events))) events]))

(defn- contact [bodies specs id other now previous]
  (let [a (bodies id) b (bodies other) sa (specs id) sb (specs other)
        offset (minus (:position b) (:position a)) distance (g/length3 offset)
        penetration (- (+ (:radius sa) (:radius sb)) distance)
        inverse-a (if (:fixed? sa) 0.0 (/ 1.0 (:mass sa 1.0)))
        inverse-b (if (:fixed? sb) 0.0 (/ 1.0 (:mass sb 1.0)))
        inverse (+ inverse-a inverse-b)]
    (if (or (neg? penetration) (zero? inverse)) [bodies nil []]
      (let [normal (if (> distance 1.0e-9) (times offset (/ 1.0 distance)) [1.0 0.0 0.0])
            speed (max 0.0 (- (dot (minus (:velocity b) (:velocity a)) normal)))
            impulse (/ (* (+ 1.0 (min (:restitution sa 0.85) (:restitution sb 0.85))) speed) inverse)
            pair [id other]
            deform-a (squash speed (:hardness sa 0.75)) deform-b (squash speed (:hardness sb 0.75))
            corrected (fn [body inv sign deformation]
                        (-> body
                            (update :position plus (times normal (* sign inv (/ penetration inverse))))
                            (update :velocity plus (times normal (* sign inv impulse)))
                            (update :deformation max deformation)))]
        [(assoc bodies id (corrected a inverse-a -1.0 deform-a) other (corrected b inverse-b 1.0 deform-b))
         pair
         (if (and (pos? speed) (not (contains? previous pair)))
           (mapv (fn [from to deformation]
                   {:type :spatial/bounce :volume-id from :other-id to :time-ms now
                    :impact-speed speed :deformation deformation}) pair (reverse pair) [deform-a deform-b])
           [])]))))

(defn step [bodies contacts ids specs {:keys [gravity bounds]} now]
  (let [accelerations (accelerations ids specs bodies gravity)
        [moved events] (reduce (fn [[out events] id]
                                 (let [[body bounces] (move-body id (specs id) (bodies id) (accelerations id) bounds now)]
                                   [(assoc out id body) (into events bounces)]))
                               [{} []] ids)
        pairs (for [i (range (count ids)) j (range (inc i) (count ids))] [(ids i) (ids j)])
        [resolved next-contacts events]
        (reduce (fn [[bodies ongoing events] [a b]]
                  (let [[bodies pair impacts] (contact bodies specs a b (+ now step-ms) contacts)]
                    [bodies (cond-> ongoing pair (conj pair)) (into events impacts)]))
                [moved #{} events] pairs)]
    {:bodies (reduce (fn [m id] (update-in m [id :position] #(constrain bounds (:radius (specs id)) %))) resolved ids)
     :contacts next-contacts :events events}))

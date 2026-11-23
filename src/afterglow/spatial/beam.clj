(ns afterglow.spatial.beam
  "Optical selection for weighted venue volumes, in metres."
  (:require [afterglow.render.frame :as frame]
            [afterglow.render.optics :as optics]
            [afterglow.render.shutter :as shutter]
            [afterglow.spatial.geometry :as geometry]
            [afterglow.time :as time]))

(defn- dot [a b] (reduce + (map * a b)))
(defn- scale [v k] (mapv #(* k %) v))
(defn- along [p d t] (mapv + p (scale d t)))

(defn- unit [v]
  (when (geometry/vec3? v)
    (let [length (geometry/length3 v)]
      (when (and (pos? length) (Double/isFinite length)) (scale v (/ 1.0 length))))))

(defn prepare-options
  "Validate optical limits and prepare receiver geometry for repeated fixture
  queries. :extinction-per-m is the current attenuation coefficient after
  accounting for fog density. A zero coefficient gives clear air."
  [{:keys [selection range-m extinction-per-m min-transmission intensity-threshold surfaces]
    :or {selection #{:beam} range-m 100.0 extinction-per-m 0.0
         min-transmission 0.01 intensity-threshold 0.0}}]
  (when-not (and (set? selection) (every? #{:beam :aimable} selection)
                 (time/finite-number? range-m) (pos? range-m)
                 (geometry/nonnegative? extinction-per-m)
                 (every? #(and (time/finite-number? %) (<= 0 % 1)) [min-transmission intensity-threshold]))
    (throw (ex-info "Invalid optical selection or range, fog, or intensity limit"
                    {:selection selection :range-m range-m :extinction-per-m extinction-per-m
                     :min-transmission min-transmission :intensity-threshold intensity-threshold})))
  {::prepared true :selection selection :extinction-per-m extinction-per-m
   :range-m (if (and (pos? extinction-per-m) (pos? min-transmission))
              (min (double range-m) (/ (- (Math/log (double min-transmission))) extinction-per-m))
              (double range-m))
   :intensity-threshold intensity-threshold
   :occluded? (when (seq surfaces) (optics/segment-occluder surfaces))})

(defn- open-gate? [{:keys [channels] :as fixture} output]
  (and (not= false (:shutter-open? output))
       (or (not (or (:shutter channels) (:strobe channels)))
           (let [gates (or (::geometry/shutters fixture) (shutter/profile channels))]
             (shutter/open? gates (fn [attr fallback] (get output attr (get (:channels output) attr fallback))))))))

(defn- light-level [fixture output]
  (let [rgb (:emitted-color output)]
    (if (and (geometry/vec3? rgb) (open-gate? fixture output))
      (max 0.0 (min 1.0 (double (reduce max rgb))))
      0.0)))

(defn- current-beam [fixture output]
  (let [pose (or (:pose output) (frame/fixture-pose fixture output))
        beam (optics/fixture-beam fixture (cond-> output pose (assoc :pose pose)))
        forward (or (:direction beam) (:direction fixture)
                    (:direction (frame/fixture-pose (dissoc fixture :calibration) {:pan 0.5 :tilt 0.5})))]
    (when-let [axis (unit forward)]
      (let [{:keys [beam-angle lens-radius-m]} beam]
        (when-not (and (time/finite-number? beam-angle) (< 0 beam-angle 180)
                       (geometry/nonnegative? lens-radius-m))
          (throw (ex-info "Invalid beam angle or lens radius" (select-keys beam [:beam-angle :lens-radius-m]))))
        (assoc beam :axis axis :spread (Math/tan (Math/toRadians (/ beam-angle 2.0))))))))

(defn- light-origin
  "Trace through the finite lens from the cone's virtual apex. This also works
  at the lens face and keeps an off-axis receiver's occlusion ray on the beam."
  [{:keys [position axis spread lens-radius-m]} point]
  (let [delta (mapv - point position)
        depth (dot delta axis)
        radial (along delta axis (- depth))
        radius (+ lens-radius-m (* spread depth))]
    (when (and (>= depth -1.0e-12) (<= (geometry/length3 radial) (+ radius 1.0e-10)))
      (along position radial (if (pos? radius) (/ lens-radius-m radius) 0.0)))))

(defn- optical-level [{:keys [range-m extinction-per-m intensity-threshold occluded?]} level origin point]
  (let [delta (mapv - point origin)
        length (geometry/length3 delta)]
    (when (<= length (+ range-m (* 8.0 (Math/ulp (double range-m)))))
      (let [received (* level (Math/exp (- (* (double extinction-per-m) length))))]
        (when (and (pos? received) (>= received intensity-threshold)
                   (or (nil? occluded?) (not (occluded? origin point length))))
          received)))))

(defn- grid-points [{low :min high :max}]
  (let [[xs ys zs] (mapv (fn [a b] [a (+ (* 0.5 a) (* 0.5 b)) b]) low high)]
    (for [x xs y ys z zs] [x y z])))

(defn- nearest-in-box [{low :min high :max} point]
  (mapv (fn [a b v] (max a (min b v))) low high point))

(defn- axis-gap ^double [^double v ^double lo ^double hi]
  (max 0.0 (max (- lo v) (- v hi))))

(defn- within-range-of-box? [point {low :min high :max} radius]
  (let [dx (axis-gap (nth point 0) (nth low 0) (nth high 0))
        dy (axis-gap (nth point 1) (nth low 1) (nth high 1))
        dz (axis-gap (nth point 2) (nth low 2) (nth high 2))
        r (double radius)]
    (<= (+ (* dx dx) (* dy dy) (* dz dz)) (* r r))))

(defn- ray-interval
  "Clip an axis segment to the half-spaces of a convex polyhedron."
  [origin axis planes reach]
  (reduce (fn [[lo hi] {:keys [normal distance]}]
            (let [s (dot normal axis)
                  d (- distance (dot normal origin))
                  interval (cond (pos? s) [lo (min hi (/ d s))]
                                 (neg? s) [(max lo (/ d s)) hi]
                                 (neg? d) nil
                                 :else [lo hi])]
              (if (and interval (<= (first interval) (second interval))) interval (reduced nil))))
          [0.0 reach] planes))

(defn- box-depths [origin axis {low :min high :max} reach]
  (let [corners (mapv (fn [a b n] (if (neg? n) [b a] [a b])) low high axis)
        depth (fn [pick] (dot (mapv - (mapv pick corners) origin) axis))
        lo (max 0.0 (depth first))
        hi (min reach (depth second))]
    (when (<= lo hi) [lo hi])))

(defn- beam-near-box?
  "Conservative rejection using the box's circumscribed sphere. A large box
  grazing the cone can pass here; actual samples decide its contribution."
  [{:keys [position axis spread lens-radius-m]} {low :min high :max} reach]
  (let [half (scale (mapv - high low) 0.5)
        r (geometry/length3 half)
        offset (mapv - (mapv + low half) position)
        depth (dot offset axis)
        far (+ depth r)]
    (and (>= far 0) (<= (- depth r) reach)
         (<= (geometry/length3 (along offset axis (- depth)))
             (+ lens-radius-m r (* spread far) 1.0e-10)))))

(defn- axis-points [{:keys [position axis spread lens-radius-m]} center [lo hi]]
  (when (and lo hi)
    (let [middle (if center (max lo (min hi (dot (mapv - center position) axis))) (/ (+ lo hi) 2.0))
          at-depth (fn [depth]
                     (let [on-axis (along position axis depth)]
                       (if center
                         (let [v (mapv - center on-axis)
                               radial (along v axis (- (dot v axis)))
                               length (geometry/length3 radial)
                               radius (+ lens-radius-m (* depth spread))]
                           [on-axis (along on-axis radial (if (zero? length) 0.0 (min 1.0 (/ radius length))))])
                         [on-axis])))]
      (mapcat at-depth [middle lo (* 0.5 (+ lo hi)) hi]))))

(defn- cross [[ax ay az] [bx by bz]]
  [(- (* ay bz) (* az by)) (- (* az bx) (* ax bz)) (- (* ax by) (* ay bx))])

(def ^:private rim-offsets
  (mapv (fn [i] (let [angle (* i (/ Math/PI 4.0))] [(Math/cos angle) (Math/sin angle)])) (range 8)))
(def ^:private cardinal-directions [[1 0 0] [-1 0 0] [0 1 0] [0 -1 0] [0 0 1] [0 0 -1]])

(defn- polyhedron-points [{:keys [position axis spread lens-radius-m]} planes reach aimable?]
  (let [ref (if (< (abs (first axis)) 0.9) [1 0 0] [0 0 1])
        u (unit (cross axis ref))
        v (cross axis u)
        rim-ray (fn [[a b]]
                  (let [radial (along (scale u a) v b)]
                    [(along position radial lens-radius-m) (unit (along axis radial spread))]))
        rays (concat [[position axis]] (map rim-ray rim-offsets)
                     (when aimable? (map #(vector position %) cardinal-directions)))
        probe (fn [[start direction]]
                (when-let [[lo hi] (ray-interval start direction planes reach)]
                  (map #(along start direction %) [lo (* 0.5 (+ lo hi)) hi])))]
    (mapcat probe rays)))

(def ^:private witness-limit 64)

(defn- shape-seeds [volume]
  ;; Prepared fields supply world-space transformed witnesses. Standalone
  ;; callers can also use plain sphere/box/cylinder leaves directly.
  (let [nodes (tree-seq #(#{:union :intersection :difference} (:shape %))
                        #(if (= :difference (:shape %)) (take 1 (:parts %)) (:parts %))
                        volume)]
    (keep (fn [{:keys [shape position radius min max]}]
            (case shape
              (:ball :sphere) {:center position :radius radius}
              (:cylinder :rounded-box) position
              :box (when (and min max) (mapv #(* 0.5 (+ %1 %2)) min max))
              nil))
          (take 128 nodes))))

(defn- square-distance [[z r] [cz cr]]
  (let [dz (- (double z) (double cz)), dr (- (double r) (double cr))]
    (+ (* dz dz) (* dr dr))))

(defn- cap-contact
  "For a finite aperture, the start of a ray depends on its angle. Locate
  minima of squared distance on the resulting cap using its tangent."
  [angle reach virtual-offset z radial]
  (let [on-cap (fn [t] [(* reach (Math/cos t))
                         (+ (* virtual-offset (Math/tan t)) (* reach (Math/sin t)))])
        derivative (fn [t]
                     (let [c (Math/cos t), s (Math/sin t)
                           [depth offset] (on-cap t)]
                       (+ (* (- z depth) reach s)
                          (* (- offset radial) (+ (* reach c) (/ virtual-offset (* c c)))))))
        minimum (fn [[left right]]
                  (when (and (<= (derivative left) 0.0) (>= (derivative right) 0.0))
                    (loop [lo (double left), hi (double right), n 0]
                      (let [mid (* 0.5 (+ lo hi))]
                        (cond (= n 45) (on-cap mid)
                              (neg? (derivative mid)) (recur mid hi (inc n))
                              :else (recur lo mid (inc n)))))))]
    (if (zero? virtual-offset)
      (on-cap (min angle (max 0.0 (Math/atan2 radial z))))
      (let [knots (map #(* angle (/ % 8.0)) (range 9))
            candidates (keep minimum (partition 2 1 knots))]
        (apply min-key #(square-distance % [z radial]) (on-cap 0.0) (on-cap angle) candidates)))))

(defn- nearest-boundary [beam reach [z radial :as target] radius]
  (let [{:keys [spread lens-radius-m]} beam
        angle (Math/atan spread), c (Math/cos angle), s (Math/sin angle)
        ;; Project onto the side, whose length along the outermost ray is reach.
        t (max 0.0 (min reach (+ (* z c) (* (- radial lens-radius-m) s))))
        side [(* t c) (+ lens-radius-m (* t s))]
        front [0.0 (min radial lens-radius-m)]
        distance #(square-distance % target)
        nearest (min-key distance side front)]
    (if (and (> (distance nearest) (* radius radius)) (>= (+ z radius) (* reach c)))
      (min-key distance nearest (cap-contact angle reach (/ lens-radius-m spread) z radial))
      nearest)))

(defn- touching-sphere-point [contact center radius]
  (let [separation (geometry/length3 (mapv - contact center))]
    (when (<= separation (+ radius 1.0e-10))
      ;; Last-bit rounding must not lose a tangent point to strict membership.
      (let [surface (if (and (pos? separation) (> separation radius))
                      (along center (mapv - contact center) (/ radius separation))
                      contact)]
        (mapv #(Math/nextAfter (double %1) (double %2)) surface center)))))

(defn- sphere-contact
  "Solve the lens disk and sloping side in the radial plane containing the
  centre. Only spheres approaching the far cap can require its refinement."
  [{:keys [position axis spread lens-radius-m] :as beam} center radius reach]
  (let [delta (mapv - center position)
        z (dot delta axis)
        transverse (along delta axis (- z))
        radial (geometry/length3 transverse)
        far (+ z radius)]
    (when (and (<= (- z radius) reach) (>= far 0.0)
               (<= (- radial radius) (+ lens-radius-m (* spread (min reach far)))))
      (let [[depth offset] (nearest-boundary beam reach [z radial] radius)
            contact (along (along position axis depth) transverse (if (pos? radial) (/ offset radial) 0.0))]
        (touching-sphere-point contact center radius)))))

(defn- near-sphere-point [origin center radius reach]
  (let [toward (mapv - origin center)
        length (geometry/length3 toward)]
    (when (and (> length reach) (<= (- length radius) reach))
      (along center toward (/ (Math/nextDown (double radius)) length)))))

(defn- seed-points [beam reach aimable? seed]
  (if (vector? seed)
    [seed]
    (let [{:keys [center radius]} seed]
      (when (geometry/vec3? center)
        (cons center
              (when (and (geometry/nonnegative? radius) (pos? radius))
                (lazy-seq
                 (remove nil? [(sphere-contact beam center radius reach)
                               (when aimable? (near-sphere-point (:position beam) center radius reach))]))))))))

(defn- candidate-points [volume {:keys [center bounds witnesses]} beam reach aimable?]
  (let [{:keys [position axis]} beam]
    (concat (when center [center])
            (when (or witnesses (#{:ball :sphere :union :intersection :difference} (:shape volume)))
              (mapcat #(seed-points beam reach aimable? %) (take witness-limit (or witnesses (shape-seeds volume)))))
            (cond bounds (concat (axis-points beam center (box-depths position axis bounds reach))
                                 [(nearest-in-box bounds position)] (grid-points bounds))
                  (= :polyhedron (:shape volume)) (polyhedron-points beam (:planes volume) reach aimable?)
                  :else (axis-points beam center [0.0 reach])))))

(defn- weighted-points [weight-at points]
  (keep (fn [point]
          (when-some [weight (weight-at point)]
            (when-not (and (time/finite-number? weight) (<= 0 weight 1))
              (throw (ex-info "Volume weight must be finite and normalized" {:point point :weight weight})))
            (when (pos? weight) [point weight])))
        (distinct points)))

(defn- best-hit [points maximum strength]
  (reduce (fn [best [point weight]]
            (if-let [received (strength point)]
              (let [w (* weight received)]
                (cond (>= w maximum) (reduced {:weight w :point point})
                      (> w (:weight best 0.0)) {:weight w :point point}
                      :else best))
              best))
          nil points))

(defn- beam-selection [points beam opts level]
  (best-hit points level (fn [point]
                     (when-let [origin (light-origin beam point)]
                       (optical-level opts level origin point)))))

(defn- aim-selection [points fixture opts origin]
  (best-hit points 1.0 (fn [point]
                     (when (frame/aim-reachable? fixture point)
                       (optical-level opts 1.0 origin point)))))

(defn- select-points [fixture beam volume sampling opts beam? aimable? level]
  (let [candidates (candidate-points volume sampling beam (:range-m opts) aimable?)
        points (weighted-points (:weight-at sampling) candidates)
        beam-hit (when beam? (beam-selection points beam opts level))
        aim-hit (when aimable? (aim-selection points fixture opts (:position beam)))]
    (when (or beam-hit aim-hit)
      (cond-> {:weight (max (:weight beam-hit 0.0) (:weight aim-hit 0.0))}
        aim-hit (assoc :aim (:point aim-hit))))))

(defn- radial-beam
  "In clear air a radial field is strongest at the nearest point of the beam.
  If a receiver hides that point or the range clips it, use the general probes."
  [{:keys [position axis spread lens-radius-m]} {:keys [center support by-distance]} opts level]
  (let [[px py pz] position [cx cy cz] center [vx vy vz] axis
        dx (- (double cx) (double px)) dy (- (double cy) (double py)) dz (- (double cz) (double pz))
        vx (double vx) vy (double vy) vz (double vz)
        z (+ (* dx vx) (* dy vy) (* dz vz))
        rx (- dx (* z vx)) ry (- dy (* z vy)) rz (- dz (* z vz))
        r (Math/sqrt (+ (* rx rx) (* ry ry) (* rz rz)))
        k (double spread) lens (double lens-radius-m)
        in? (and (>= z 0.0) (<= r (+ lens (* k z))))
        ;; Closest point to the side of the infinite frustum in its meridian.
        side-z (max 0.0 (/ (+ z (* k (- r lens))) (+ 1.0 (* k k))))
        side-r (+ lens (* side-z k))
        front-r (min r lens)
        side-gap (Math/hypot (- side-z z) (- side-r r))
        front-gap (Math/hypot z (- front-r r))
        face? (< front-gap side-gap)
        gap (cond in? 0.0 face? front-gap :else side-gap)]
    (when (<= gap (Math/nextUp (double support)))
      (let [axial (cond in? z face? 0.0 :else side-z)
            radial (cond in? r face? front-r :else side-r)
            factor (if (pos? r) (/ radial r) 0.0)
            hit (if in? center [(+ px (* axial vx) (* factor rx))
                                (+ py (* axial vy) (* factor ry))
                                (+ pz (* axial vz) (* factor rz))])
            aperture (* factor (/ lens (+ lens (* k axial) 1.0e-300)))
            origin (if (zero? aperture) position [(+ px (* aperture rx)) (+ py (* aperture ry)) (+ pz (* aperture rz))])
            distance (Math/hypot axial (- radial (* aperture r)))
            value (by-distance (min gap (double support)))]
        (cond (not (pos? value)) nil
              (or (> distance (:range-m opts))
                  (when-let [blocked? (:occluded? opts)] (blocked? origin hit distance))) ::probe
              :else {:weight (* level value)})))))

(defn contribution
  "Return nil or {:weight w, optional :aim [x y z]} for one fixture and volume.
  Sampling supplies :weight-at, optional world AABB :bounds and :center.
  :beam tests actual emitted RGB with calibrated pose, beam angle, lens and
  occlusion. :aimable can suggest a reachable point for a dark moving head.
  Pass prepared options when querying many fixtures."
  [fixture output volume {:keys [bounds] :as sampling} options]
  (let [{:keys [selection range-m intensity-threshold] :as opts}
        (if (::prepared options) options (prepare-options options))
        level (light-level fixture output)
        illuminated? (and (:beam selection) (pos? level) (>= level intensity-threshold))
        aimable? (and (:aimable selection) (every? #(contains? (:channels fixture) %) [:pan :tilt]))
        origin (:position fixture [0 0 0])]
    (when (and (or illuminated? aimable?)
               (or (nil? bounds)
                   (within-range-of-box? origin bounds (+ range-m (double (:lens-radius-m fixture 0.119))))))
      (when-let [beam (current-beam fixture output)]
        (let [beam? (and illuminated? (or (nil? bounds) (beam-near-box? beam bounds range-m)))]
          (when (or beam? aimable?)
            (if (and beam? (not aimable?) (:radial sampling) (zero? (:extinction-per-m opts)))
              (let [result (radial-beam beam (:radial sampling) opts level)]
                (if (= ::probe result) (select-points fixture beam volume sampling opts true false level) result))
              (select-points fixture beam volume sampling opts beam? aimable? level))))))))

(ns afterglow.render.optics
  "Pure planar receiver geometry in world metres. Beam angles are full included degrees.")

(defn- finite? [x]
  (and (number? x) #?(:clj (Double/isFinite (double x)) :cljs (js/Number.isFinite x))))

(defn- xyz [v label]
  (when-not (and (sequential? v) (= 3 (count v)) (every? finite? v))
    (throw (ex-info "Expected three finite coordinates" {:field label :value v})))
  (mapv double v))

(defn- dot [[x y z] [a b c]] (+ (* x a) (* y b) (* z c)))
(defn- scale [v k] (mapv #(* % k) v))
(defn- add [a b] (mapv + a b))
(defn- sub [a b] (mapv - a b))
(defn- cross [[x y z] [a b c]] [(- (* y c) (* z b)) (- (* z a) (* x c)) (- (* x b) (* y a))])
(defn- magnitude [[x y z]] (Math/hypot (Math/hypot x y) z))

(defn- unit [v]
  (let [length (magnitude v)]
    (when (and (finite? length) (pos? length)) (mapv #(/ % length) v))))

(defn- axis [v label]
  (or (unit (xyz v label)) (throw (ex-info "Expected a nonzero axis" {:field label :value v}))))

(defn- project-onto-plane [v normal] (sub v (scale normal (dot v normal))))

(defn- plane [{:keys [id point normal size u-axis]}]
  (when (nil? id) (throw (ex-info "Receiver needs a surface ID" {})))
  (when-not (or (nil? size) (and (sequential? size) (= 2 (count size)) (every? #(and (finite? %) (pos? %)) size)))
    (throw (ex-info "Receiver size must contain two positive lengths" {:size size})))
  (let [n (axis normal :normal)
        ref (if u-axis (axis u-axis :u-axis)
                (if (< (abs (first n)) 0.9) [1.0 0.0 0.0] [0.0 0.0 1.0]))
        projected (project-onto-plane ref n)]
    (when (< (magnitude projected) 1.0e-10)
      (throw (ex-info "Receiver's horizontal axis is parallel to its normal" {:u-axis ref :normal n})))
    (let [u (unit projected)]
      {:id id :point (xyz point :point) :normal n :u u :v (cross n u) :size size})))

(defn- aperture [{:keys [position beam-angle lens-radius-m] :or {lens-radius-m 0}}]
  (when-not (and (finite? beam-angle) (< 0.0 beam-angle 180.0)
                 (finite? lens-radius-m) (not (neg? lens-radius-m)))
    (throw (ex-info "Beam needs a full angle between 0 and 180 degrees and a nonnegative lens radius"
                    {:beam-angle beam-angle :lens-radius-m lens-radius-m})))
  {:origin (xyz position :position)
   :half-angle (* (/ Math/PI 360.0) (double beam-angle))
   :radius (double lens-radius-m)})

(defn fixture-beam
  "Describe the light leaving a fixture in a committed frame. A :pose's world
  direction takes precedence over the requested direction. Zoom ranges and
  explicit beam angles are full included degrees; a fixed angle stays fixed."
  [fixture output]
  (let [zoom (get output :zoom (get-in output [:channels :zoom] 0.0))
        [narrow wide] (:zoom-range-deg fixture)]
    {:position (:position fixture [0.0 0.0 0.0])
     :direction (or (get-in output [:pose :direction]) (:direction output))
     :beam-angle (if (and narrow wide) (+ narrow (* zoom (- wide narrow)))
                     (get fixture :beam-angle (+ 12.0 (* 34.0 zoom))))
     :lens-radius-m (:lens-radius-m fixture 0.119)}))

(defn- ray-hit [{:keys [origin direction]} {:keys [point normal u v size]}]
  (let [incidence (dot direction normal)]
    (when (> (abs incidence) 1.0e-10)
      (let [distance (/ (dot (sub point origin) normal) incidence)]
        (when (and (finite? distance) (> distance 0.0))
          (let [hit (add origin (scale direction distance))
                offset (sub hit point)]
            (when (or (nil? size)
                      (and (<= (abs (dot offset u)) (* 0.5 (first size)))
                           (<= (abs (dot offset v)) (* 0.5 (second size)))))
              {:hit hit :distance-m distance})))))))

(defn- extent [major minor a b direction]
  (Math/hypot (* a (dot major direction)) (* b (dot minor direction))))

(defn- ellipse [{:keys [origin direction radius half-angle]}
                {:keys [id point normal u v size]} hit]
  (let [signed (dot direction normal)
        n (if (pos? signed) (scale normal -1.0) normal)
        incidence (abs signed)
        sin-b (Math/sin half-angle)
        cos-b (Math/cos half-angle)
        ;; Intersection ceases to be a bounded ellipse at grazing incidence.
        k (- (* incidence incidence) (* sin-b sin-b))]
    (when (> k 1.0e-12)
      (let [virtual-apex (sub origin (scale direction (/ radius (Math/tan half-angle))))
            height (dot (sub virtual-apex point) n)
            transverse (project-onto-plane direction n)
            major (or (when (> (magnitude transverse) 1.0e-12) (unit transverse)) u)
            minor (unit (cross n major))
            a (/ (* height sin-b cos-b) k)
            b (/ (* height sin-b) (Math/sqrt k))
            ;; Translate from the centre-ray hit; this also avoids subtracting
            ;; the potentially distant virtual apex when locating the centre.
            center (add (:hit hit) (scale transverse (/ (* height sin-b sin-b) (* incidence k))))
            offset (sub center point)]
        (when (and (finite? a) (finite? b) (every? finite? center)
                   ;; A receiver that cuts through the aperture would need a
                   ;; truncated conic, rather than the entire optical ellipse.
                   (>= (- (dot (sub center origin) direction) (extent major minor a b direction)) -1.0e-9))
          (merge hit {:surface-id id :center center :normal n
                      :major-axis major :minor-axis minor :major-radius-m a :minor-radius-m b
                      :clipped? (boolean
                                 (and size
                                      (some (fn [[direction length]]
                                              (> (+ (abs (dot offset direction)) (extent major minor a b direction))
                                                 (+ (* 0.5 length) 1.0e-9)))
                                            [[u (first size)] [v (second size)]])))}))))))

(defn beam-footprint
  "Intersect a beam's centre ray and circular cone with a two-sided planar
  receiver. The beam position is its lens centre. Supply :direction, full
  :beam-angle and optional :lens-radius-m. The surface needs :id, :point and
  :normal, plus optional :u-axis and :size [width height] for a rectangle.
  Return nil for a centre-ray miss or an unbounded or aperture-crossing spot.
  :clipped? marks an ellipse extending past the finite receiver."
  [beam surface]
  (let [beam (assoc (aperture beam) :direction (axis (:direction beam) :direction))
        receiver (plane surface)]
    (when-let [hit (ray-hit beam receiver)]
      (ellipse beam receiver hit))))

(defn nearest-footprint
  "Return the footprint on the first receiver struck by the beam's centre ray.
  An unbounded first hit occludes later surfaces. Input order breaks exact ties."
  [beam surfaces]
  (let [ray (assoc (aperture beam) :direction (axis (:direction beam) :direction))]
    (when-let [[surface hit]
               (reduce (fn [best surface]
                         (let [receiver (plane surface)
                               hit (ray-hit ray receiver)]
                           (if (and hit (or (nil? best) (< (:distance-m hit) (:distance-m (second best)))))
                             [receiver hit] best)))
                       nil surfaces)]
      (ellipse ray surface hit))))

(defn- support-point [{:keys [center major-axis minor-axis major-radius-m minor-radius-m]} direction]
  (let [x (* major-radius-m (dot major-axis direction))
        y (* minor-radius-m (dot minor-axis direction))
        length (Math/hypot x y)]
    (-> center
        (add (scale major-axis (* major-radius-m (/ x length))))
        (add (scale minor-axis (* minor-radius-m (/ y length)))))))

(defn edge-aim
  "Aim a follower so its elliptical spot touches a leader footprint on the
  specified surface, on the side of world vector along. Return a world :aim
  (axis hit), :direction, tangent :contact and new :footprint. Returns nil when
  the spots cannot fit wholly on the receiver or the geometry is degenerate.
  Reuse the returned footprint and the same along vector for adjacent heads."
  [leader follower surface along]
  (let [{:keys [origin radius half-angle]} (aperture follower)
        {:keys [id normal] :as receiver} (plane surface)
        along (project-onto-plane (axis along :along) normal)]
    (when (and (= (:surface-id leader) id) (not (:clipped? leader)) (> (magnitude along) 1.0e-10))
      (let [side (unit along)
            tangent (unit (cross normal side))
            contact (support-point leader side)
            offset (project-onto-plane (sub origin contact) tangent)
            length (magnitude offset)
            aperture-distance (* radius (Math/cos half-angle))]
        (when (> length aperture-distance)
          ;; The common tangent plane contains the contact line. The lens centre
          ;; lies radius*cos(half-angle) inside this plane. Two planes satisfy
          ;; that offset; keep the solution on the follower side of the line.
          (let [base (unit offset)
                ratio (/ aperture-distance length)
                perp (scale (cross tangent base) (Math/sqrt (- 1.0 (* ratio ratio))))
                base (scale base ratio)]
            (some (fn [inward]
                    (when (> (dot inward side) 1.0e-10)
                      (when-let [generator (unit (project-onto-plane (sub contact origin) inward))]
                        (let [direction (unit (add (scale generator (Math/cos half-angle))
                                                   (scale inward (Math/sin half-angle))))
                              ray (assoc (aperture follower) :direction direction)]
                          (when-let [hit (ray-hit ray receiver)]
                            (when-let [spot (ellipse ray receiver hit)]
                              (when-not (:clipped? spot)
                                {:aim (:hit spot) :direction direction :contact contact :footprint spot})))))))
                  [(add base perp) (sub base perp)])))))))

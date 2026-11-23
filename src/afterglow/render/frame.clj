(ns afterglow.render.frame
  "Deterministic fixture resolution and owned DMX packing without I/O.

  Inputs use linear RGB and normalized scalar attributes [0,1]. Geometry uses
  metres, +Y up, a local forward direction of +Z, positive yaw toward +X and
  positive elevation toward +Y. This is a new explicit fixture contract, not
  an implementation of all legacy fixture function ranges/optics."
  (:require [afterglow.render.atmosphere :as atmosphere]
            [afterglow.render.coverage :as coverage]
            [afterglow.render.emission.dense :as emission]
            [afterglow.render.layers :as layers]
            [afterglow.render.hdr :as hdr]
            [afterglow.render.hdr.packed :as packed-hdr]
            [afterglow.render.optics :as optics]
            [afterglow.render.photometry :as photometry]
            [afterglow.runtime.faults :as faults]))

(def ^:private emitter-attributes (set (keys photometry/emitter-spectrum)))
(def ^:private extra-emitters (apply dissoc photometry/emitter-spectrum [:red :green :blue :white]))
(def ^:private geometric-attributes #{:aim :direction})
(def ^:private rgb-attributes [:red :green :blue])

;; Final fields, no mutable buffers: safe to share between render workers/frames.
(deftype ChannelScatter [^long universe ^long index ^long fineUniverse ^long fineIndex ^double pivot])
(deftype DenseChannel [^long kind ^long slot ^long compactIndex scatter fallback])
(deftype EmitterTint [attribute ^long slot ^double red ^double green ^double blue])
(deftype DenseFixture [^boolean emitter ^boolean dimmer ^boolean extractMin emission channels tints])
(def ^:private compact-specs
  [[:pan :number 1] [:tilt :number 1] [:focus :number 1] [:zoom :number 1] [:strobe :number 1]
   [:emitted-color :vec3 3] [:intensity :number 1] [:aim :vec3 3] [:direction :vec3 3]])
(def ^:private compact-channel-indices {:pan 0 :tilt 1 :focus 2 :zoom 3 :strobe 4 :shutter 9})

(defn- packed-number? [value]
  (or (instance? Double value) (instance? Float value) (integer? value)))

(defn- fail! [message data]
  (throw (ex-info message (assoc data :type ::invalid-frame))))

(defmacro ^:private with-effect-source [source & body]
  `(try ~@body
        (catch Exception error# (throw (faults/attributed-error error# ~source)))))

(defn- finite? [x]
  (and (number? x) (Double/isFinite (double x))))

(defn- unit? [x] (and (finite? x) (<= 0 x) (<= x 1)))
(defn- vec3? [x] (and (vector? x) (= 3 (count x)) (every? finite? x)))
(defn- positive-int? [x] (and (integer? x) (pos? x) (<= x Integer/MAX_VALUE)))
(defn- clamp [x lo hi] (min hi (max lo x)))

(defn- channel-spec [spec]
  (cond (integer? spec) {:offset spec}
        (and (vector? spec) (= 2 (count spec))) {:offset (first spec) :fine-offset (second spec)}
        (map? spec) spec
        :else nil))

(defn- channel-address [fixture offset]
  (let [linear (+ (- (:address fixture) 1) (- offset 1))
        universe (+ (:universe fixture) (quot linear 512))]
    (when (> universe Integer/MAX_VALUE)
      (fail! "Fixture span exceeds supported universe range" {:fixture-id (:id fixture) :universe universe}))
    [universe (mod linear 512)]))

(defn- calibration-valid? [spec]
  (or (nil? spec)
      (and (vector? spec) (= 2 (count spec)) (every? finite? spec)
           (<= 0 (first spec) 255) (not (zero? (second spec))))
      (and (map? spec) (finite? (:min-deg spec)) (finite? (:max-deg spec))
           (finite? (- (:max-deg spec) (:min-deg spec)))
           (< (:min-deg spec) (:max-deg spec)))))

(defn- compile-scatter [universe-indices attribute {:keys [coarse fine inverted-from] :as channel}]
  (assoc channel ::compact-index (get compact-channel-indices attribute)
         ::scatter (when (or (nil? inverted-from) (packed-number? inverted-from))
                     (ChannelScatter. (long (get universe-indices (first coarse))) (long (second coarse))
                                      (long (if fine (get universe-indices (first fine)) -1))
                                      (long (if fine (second fine) -1)) (double (or inverted-from -1.0))))))

(defn- validate-footprints! [fixtures slots]
  (when (some #(contains? % :footprint) fixtures)
    (doseq [fixture fixtures :when (contains? fixture :footprint)]
      (let [footprint (:footprint fixture)
            mapped (mapcat (fn [[_ channel]] (remove nil? [(:offset channel) (:fine-offset channel)]))
                           (:compiled-channels fixture))]
        (when-not (and (positive-int? footprint) (every? #(<= % footprint) mapped))
          (fail! "Explicit fixture footprint must be positive and cover every mapped offset"
                 {:fixture-id (:id fixture) :footprint footprint}))
        ;; Validate the physical end without allocating one entry per reserved
        ;; byte; a sparse mode may reserve a large span with few mapped channels.
        (channel-address fixture footprint)))
    (let [reserved-ids (into #{} (keep #(when (contains? % :footprint) (:id %))) fixtures)
          ranges (concat
                   (for [fixture fixtures :when (contains? fixture :footprint)
                         :let [start (+ (* (long (:universe fixture)) 512) (dec (:address fixture)))]]
                     {:fixture-id (:id fixture) :start start :end (+ start (dec (:footprint fixture)))})
                   (for [{:keys [fixture-id slot]} slots :when (not (contains? reserved-ids fixture-id))
                         :let [start (+ (* (long (first slot)) 512) (second slot))]]
                     {:fixture-id fixture-id :start start :end start}))]
      (doseq [[left right] (partition 2 1 (sort-by :start ranges))]
        (when (<= (:start right) (:end left))
          (fail! "Fixture physical footprints overlap" {:left left :right right}))))))

(defn compile-patch
  "Validate and compile fixtures to reusable immutable channel scatter metadata.

  Channel offsets are 1-based relative to fixture :address. Crossing address 512
  advances the universe, including fine channels. Channel values are an offset,
  [coarse fine], or {:offset n :fine-offset n :inverted-from 0|1|...255}.
  :rgbw-policy is :none or :extract-min (requires a white channel).
  Optional :rotation-deg is [x y z], applied X then Y then Z.
  Axis calibration is {:min-deg a :max-deg b}, or legacy [center half-circle]
  values in DMX units. Optional :footprint reserves every physical channel in
  that span and must cover all mapped coarse/fine offsets. Without it only mapped
  channels are reserved. Compilation rejects duplicate IDs and all collisions."
  [fixtures]
  (when-not (vector? fixtures) (fail! "Fixtures must be a vector" {:path [:fixtures]}))
  (when-not (= (count fixtures) (count (set (map :id fixtures))))
    (fail! "Fixture IDs must be unique" {:path [:fixtures]}))
  (let [compiled
        (mapv
         (fn [index fixture]
           (let [{:keys [id position surface-uv universe address channels calibration]} fixture]
             (when (and (some? surface-uv)
                        (not (and (vector? surface-uv) (= 2 (count surface-uv)) (every? finite? surface-uv))))
               (fail! "Fixture surface UV must contain two finite coordinates"
                      {:path [:fixtures index :surface-uv] :fixture-id id}))
             (when (contains? fixture :fogger) (atmosphere/validate-fogger! fixture))
             (when-let [{:keys [path message]} (first (photometry/errors fixture))]
               (fail! message {:path (into [:fixtures index] path) :fixture-id id}))
             (when-not (and (map? fixture) (some? id)
                            (vec3? (or position [0 0 0]))
                            (integer? universe) (<= 0 universe Integer/MAX_VALUE)
                            (integer? address) (<= 1 address 512)
                            (map? channels) (seq channels) (every? keyword? (keys channels))
                            (not-any? #{:color :aim :direction} (keys channels))
                            (or (nil? calibration) (map? calibration))
                            (calibration-valid? (:pan calibration))
                            (calibration-valid? (:tilt calibration))
                            (or (nil? (:emission-color fixture))
                                (and (vec3? (:emission-color fixture)) (every? unit? (:emission-color fixture))))
                            (vec3? (:rotation-deg fixture [0 0 0])))
               (fail! "Invalid fixture identity, position, patch, rotation or calibration" {:fixture-id id}))
             (when-not (#{:none :extract-min} (:rgbw-policy fixture :none))
               (fail! "Unsupported RGBW policy" {:fixture-id id :policy (:rgbw-policy fixture)}))
             (when (and (= :extract-min (:rgbw-policy fixture)) (not (contains? channels :white)))
               (fail! "White extraction requires a white channel" {:fixture-id id}))
             (assoc fixture :position (or position [0 0 0])
                    :emission-color (or (:emission-color fixture) [1.0 1.0 1.0])
                    ::index index
                    ::emitter? (boolean (some #(contains? channels %) emitter-attributes))
                    ::dimmer? (contains? channels :dimmer)
                    ::rgb? (every? #(contains? channels %) rgb-attributes)
                    ::supported (cond-> (conj (set (keys channels)) :dimmer)
                                  (every? #(contains? channels %) rgb-attributes) (conj :color)
                                  (and (contains? channels :pan) (contains? channels :tilt)) (conj :aim :direction))
                    :compiled-channels
                    (into {}
                          (for [[attribute spec] channels]
                            (let [{:keys [offset fine-offset inverted-from] :as normalized} (channel-spec spec)]
                              (when-not (and normalized (positive-int? offset)
                                             (or (nil? fine-offset) (positive-int? fine-offset))
                                             (or (nil? inverted-from)
                                                 (and (finite? inverted-from) (<= 0 inverted-from 255))))
                                (fail! "Invalid channel offset or inversion" {:fixture-id id :attribute attribute}))
                              [attribute (assoc normalized :coarse (channel-address fixture offset)
                                                :fine (when fine-offset (channel-address fixture fine-offset)))]))))))
         (range) fixtures)
        slots (vec (for [fixture compiled
                         [attribute spec] (:compiled-channels fixture)
                         slot (remove nil? [(:coarse spec) (:fine spec)])]
                     {:slot slot :fixture-id (:id fixture) :attribute attribute}))
        collisions (filter #(> (count (val %)) 1) (group-by :slot slots))]
    (when (seq collisions)
      (fail! "Fixture channels overlap" {:collisions (into {} collisions)}))
    (validate-footprints! compiled slots)
    (let [universes (vec (sort (set (map (comp first :slot) slots))))
          universe-indices (zipmap universes (range))
          compiled (mapv
                    (fn [fixture]
                      (let [channels (:compiled-channels fixture)
                            channels (into {} (map (fn [[attr channel]]
                                                     [attr (compile-scatter universe-indices attr channel)])) channels)
                            emitters (select-keys channels emitter-attributes)
                            lamp? (and (:dimmer channels)
                                       (not-any? channels [:fog :haze :fan :relay :pump]))
                            light (when (or (seq emitters) lamp?)
                                    (cond-> emitters (:dimmer channels) (assoc :dimmer (:dimmer channels))))]
                        (assoc fixture :compiled-channels channels ::emission-channels light)))
                    compiled)
          base-attributes [:dimmer :red :green :blue :white :amber :uv]
          extra-attributes (sort (remove (set base-attributes) (set (mapcat (comp keys :channels) compiled))))
          attribute-slots (zipmap (concat base-attributes extra-attributes) (range 3 (+ 10 (count extra-attributes))))
          compiled (mapv (fn [{:keys [channels] :as fixture}]
                           (cond-> (assoc fixture ::tints
                                  (vec (for [[attr [response [r g b]]] extra-emitters
                                             :when (and (pos? response) (contains? channels attr))]
                                         (EmitterTint. attr (get attribute-slots attr) r g b))))
                             (:fogger fixture)
                             (update-in [:compiled-channels :fog] assoc
                                        ::fog-off (atmosphere/off-bytes fixture)
                                        ::fog-idle-level (atmosphere/physical-level
                                                           (get-in fixture [:compiled-channels :fog])
                                                           (first (get-in fixture [:fogger :dmx-range] [0 255]))))))
                         compiled)]
      {:type ::patch ::hdr-layout (delay (hdr/layout compiled attribute-slots))
       ::emission-layout (emission/compile-layout compiled universes ::emission-channels)
       :fog-off-bytes (into {} (mapcat #(get-in % [:compiled-channels :fog ::fog-off])) compiled)
       :fixtures compiled :by-id (into {} (map (juxt :id identity) compiled))
       ::moving-heads (filterv #(contains? (::supported %) :aim) compiled)
       :target-order (mapv :id compiled) ::attribute-slots attribute-slots
       ::stride (+ 10 (count extra-attributes))
       ::dense-fixtures
       (mapv (fn [fixture]
               (DenseFixture.
                (::emitter? fixture) (::dimmer? fixture) (= :extract-min (:rgbw-policy fixture))
                (:emission-color fixture [1.0 1.0 1.0])
                (mapv (fn [[attribute channel]]
                        (DenseChannel. (long (case attribute :dimmer 0 :red 1 :green 2 :blue 3 :white 4 :fog (if (::fog-off channel) 7 6) (if (contains? extra-emitters attribute) 5 6)))
                                       (long (get attribute-slots attribute))
                                       (long (or (::compact-index channel) -1))
                                       (::scatter channel) channel)) (:compiled-channels fixture))
                (::tints fixture))) compiled)
       ::common-attributes (if (seq compiled)
                             (reduce (fn [common fixture] (into #{} (filter (::supported fixture)) common))
                                     (::supported (first compiled)) (rest compiled)) #{})
       :universes universes})))

(defn validate-patch
  "Return [] when a patch compiles, otherwise structured validation errors."
  [fixtures]
  (try (compile-patch fixtures) []
       (catch clojure.lang.ExceptionInfo error
         [(assoc (ex-data error) :message (.getMessage error))])))

(defn- blend-value [previous value blend opacity]
  (let [op (case blend :replace (fn [_ value] value) :max max :add +)
        composite (if (== 1 opacity) op (fn [before value] (+ before (* opacity (- (op before value) before)))))]
    (if (vector? value)
      (mapv composite (or previous (vec (repeat (count value) 0))) value)
      (composite (or previous 0) value))))

(defn- assignment-value? [attribute value hdr?]
  (let [level? (if (and hdr? (hdr/light-attributes attribute))
                 #(and (finite? %) (not (neg? %))) unit?)]
    (case attribute
      :color (and (vec3? value) (every? level? value))
      (:aim :direction) (vec3? value)
      (level? value))))

(defn- validate-assignment! [fixture target-id attribute value blend assignment hdr?]
  (when-not (and (map? assignment) fixture
                 (keyword? attribute) (#{:replace :max :add} blend)
                 (assignment-value? attribute value (and hdr? (::emission-channels fixture))) (unit? (:opacity assignment 1)))
    (fail! "Invalid assignment target, attribute, blend or value" {:assignment assignment}))
  (when (and (= attribute :color) (not (::rgb? fixture)))
    (fail! "Color assignment requires red, green and blue channels" {:target-id target-id}))
  (when-not (contains? (::supported fixture) attribute)
    (fail! "Fixture does not implement assigned attribute" {:target-id target-id :attribute attribute}))
  (when (and (contains? geometric-attributes attribute) (not= :replace blend))
    (fail! "Geometry assignments require :replace blend" {:target-id target-id :attribute attribute})))

(defn- merge-general-assignments!
  [patch ^objects targets assignments ^objects geometry-sources source]
  (let [by-id (:by-id patch)]
    (doseq [{:keys [target-id attribute value blend opacity] :or {blend :replace opacity 1} :as assignment} assignments]
      (let [fixture (get by-id target-id)]
        (validate-assignment! fixture target-id attribute value blend assignment (::hdr? patch))
        (when (pos? opacity)
          (let [index (int (::index fixture))
                attributes (or (aget targets index) (transient {}))
                previous (get attributes attribute)
                blended (blend-value previous value blend opacity)]
            (when-not (assignment-value? attribute blended (and (::hdr? patch) (::emission-channels fixture)))
              (fail! "Blended assignment exceeds its finite attribute range" {:target-id target-id :attribute attribute :value blended}))
            (aset targets index (assoc! attributes attribute blended))
            (when (and geometry-sources (geometric-attributes attribute))
              ;; Nil deliberately clears an earlier attributed write. An unattributed
              ;; replacement must not blame the effect that it superseded.
              (aset geometry-sources index (assoc (aget geometry-sources index) attribute source)))))))))

(defn- persist-assignments! [^objects targets]
  (dotimes [index (alength targets)]
    (when-let [attributes (aget targets index)]
      (aset targets index (persistent! attributes))))
  targets)

(defn- reduce-assignments [patch assignments]
  (when-not (vector? assignments) (fail! "Assignments must be a vector" {}))
  ;; Scratch storage is private to this evaluation. Stable target indices avoid
  ;; rebuilding the outer persistent map for every per-pixel contribution.
  (let [targets (object-array (count (:fixtures patch)))]
    (merge-general-assignments! patch targets assignments nil nil)
    (persist-assignments! targets)))

(defn- rotate [v axis radians]
  (let [[x y z] v, c (Math/cos radians), s (Math/sin radians)]
    (case axis
      :x [x (- (* y c) (* z s)) (+ (* y s) (* z c))]
      :y [(+ (* x c) (* z s)) y (- (* z c) (* x s))]
      :z [(- (* x c) (* y s)) (+ (* x s) (* y c)) z])))

(defn- local-direction [fixture direction]
  (let [[x y z] (:rotation-deg fixture [0 0 0])]
    (-> direction
        (rotate :z (Math/toRadians (- (double z))))
        (rotate :y (Math/toRadians (- (double y))))
        (rotate :x (Math/toRadians (- (double x)))))))

(defn- axis-calibration [fixture axis]
  (or (get-in fixture [:calibration axis])
      (if (= axis :pan) {:min-deg -180 :max-deg 180} {:min-deg -90 :max-deg 90})))

(defn- mechanical-degrees [fixture axis value]
  (let [calibration (axis-calibration fixture axis)]
    (if (vector? calibration)
      (let [[center half-circle] calibration]
        (* 180.0 (/ (- (* 255.0 value) center) half-circle)))
      (let [{:keys [min-deg max-deg]} calibration]
        (+ min-deg (* (double value) (- max-deg min-deg)))))))

(defn fixture-pose
  "Project the committed normalized pan/tilt command through the fixture's
  calibration and mount rotation. Works on rich or projected compact target
  values. Degrees retain mechanical travel through wraps. The unit direction
  is in world space. Returns nil when either channel value is unavailable.
  An aimed point and its requested angles remain separate in the original
  output. Call on selected heads when their pose is needed."
  [fixture output]
  (let [pan (get output :pan (get-in output [:channels :pan]))
        tilt (get output :tilt (get-in output [:channels :tilt]))]
    (when (and (unit? pan) (unit? tilt))
      (let [yaw (mechanical-degrees fixture :pan pan)
            elevation (mechanical-degrees fixture :tilt tilt)
            p (Math/toRadians yaw)
            t (Math/toRadians elevation)
            horizontal (Math/cos t)
            [x y z] (:rotation-deg fixture [0 0 0])]
        {:pan-deg yaw :tilt-deg elevation
         :direction (-> [(* (Math/sin p) horizontal) (Math/sin t) (* (Math/cos p) horizontal)]
                        (rotate :x (Math/toRadians (double x)))
                        (rotate :y (Math/toRadians (double y)))
                        (rotate :z (Math/toRadians (double z))))}))))

(defn- normalized-angle [fixture axis degrees previous]
  (let [calibration (axis-calibration fixture axis)
        convert (if (vector? calibration)
                  (fn [angle] (/ (+ (first calibration) (* (/ angle 180.0) (second calibration))) 255.0))
                  (fn [angle] (/ (- angle (:min-deg calibration))
                                 (- (:max-deg calibration) (:min-deg calibration)))))
        candidates (if (= axis :pan) (mapv convert [degrees (- degrees 360) (+ degrees 360)]) [(convert degrees)])
        legal (filterv unit? candidates)
        target (or previous (convert 0))
        nearest (first (sort-by #(Math/abs (double (- % target))) (if (seq legal) legal candidates)))]
    {:value (clamp nearest 0 1) :reachable? (boolean (seq legal)) :degrees degrees}))

(defn- check-movement-history! [fixture previous]
  (doseq [axis [:pan :tilt] :let [value (get previous axis)]]
    (when (and (some? value) (not (unit? value)))
      (fail! "Previous pan/tilt must be normalized finite values" {:fixture-id (:id fixture) :axis axis}))))

(defn- resolve-geometry [fixture assigned previous source]
  (if (or (:aim assigned) (:direction assigned))
    (do
      (check-movement-history! fixture previous)
      (with-effect-source source
        (let [direction (if (:aim assigned) (mapv - (:aim assigned) (:position fixture)) (:direction assigned))
              [x y z] (local-direction fixture direction)
              magnitude (Math/sqrt (+ (* x x) (* y y) (* z z)))]
          (when-not (and (finite? magnitude) (pos? magnitude))
            (fail! "Aim/direction must have finite nonzero distance" {:fixture-id (:id fixture)}))
          (when-not (and (contains? (:channels fixture) :pan) (contains? (:channels fixture) :tilt))
            (fail! "Aim/direction requires pan and tilt channels" {:fixture-id (:id fixture)}))
          (let [pan-deg (Math/toDegrees (Math/atan2 x z))
                tilt-deg (Math/toDegrees (Math/atan2 y (Math/sqrt (+ (* x x) (* z z)))))
                pan (normalized-angle fixture :pan pan-deg (:pan previous))
                tilt (normalized-angle fixture :tilt tilt-deg (:tilt previous))]
            ;; Explicit geometric output takes precedence over direct pan/tilt.
            ;; Attributes inside one kind retain input order.
            (assoc assigned :pan (:value pan) :tilt (:value tilt)
                   :pan-deg pan-deg :tilt-deg tilt-deg
                   :direction (mapv #(/ % magnitude) direction)
                   :aim-reachable? (and (:reachable? pan) (:reachable? tilt)))))))
    assigned))

(defn aim-reachable?
  "Can the calibrated physical renderer point this head's centre ray at a world
  point in metres? Fixed fixtures and a target at the lens have no aim solution."
  [fixture point]
  (let [origin (:position fixture [0 0 0])]
    (boolean (and (contains? (:channels fixture) :pan) (contains? (:channels fixture) :tilt)
                  (vec3? point) (not (every? zero? (map - point origin)))
                  (:aim-reachable? (resolve-geometry (assoc fixture :position origin) {:aim point} nil nil))))))

(defn- apply-solved-geometry [fixture assigned previous solution source]
  (check-movement-history! fixture previous)
  (with-effect-source source
    (let [{:keys [pan tilt pan-deg tilt-deg aim-reachable?]} solution
          direction (if (:aim assigned) (mapv - (:aim assigned) (:position fixture)) (:direction assigned))
          [x y z] (mapv double direction)
          magnitude (Math/sqrt (+ (* x x) (* y y) (* z z)))]
      (when-not (and (unit? pan) (unit? tilt) (finite? pan-deg) (finite? tilt-deg)
                     (boolean? aim-reachable?) (Double/isFinite magnitude) (pos? magnitude))
        (fail! "Invalid calibrated movement result" {:fixture-id (:id fixture)}))
      (assoc assigned :direction (mapv #(/ % magnitude) direction)
             :pan pan :tilt tilt :pan-deg pan-deg :tilt-deg tilt-deg :aim-reachable? aim-reachable?))))

(declare pack-value!)

(defn- create-buffers [patch]
  (let [indexed (object-array (map (fn [_] (byte-array 512)) (:universes patch)))]
    {:indexed indexed :universes (into (sorted-map) (map-indexed (fn [i u] [u (aget indexed i)]) (:universes patch)))}))

(defn- write-off-bytes! [universes off-bytes]
  (reduce-kv (fn [_ [u index] value]
               (aset-byte ^bytes (get universes u) (int index) (unchecked-byte value))
               nil) nil off-bytes))

(defn idle-universes
  "New, exclusively owned shutdown buffers. Fog uses its physical off endpoint.
  Every other byte starts at zero."
  [patch]
  (let [buffers (:universes (create-buffers patch))]
    (write-off-bytes! buffers (:fog-off-bytes patch))
    buffers))

(defn- pack-scatter! [^objects buffers ^ChannelScatter channel ^double level]
  (let [value (* 255.0 level)
        pivot (.-pivot channel)
        value (if (and (>= pivot 0.0) (>= value pivot)) (- 255.0 (- value pivot)) value)
        ^bytes coarse (aget buffers (int (.-universe channel)))
        index (int (.-index channel))]
    (if (neg? (.-fineUniverse channel))
      (aset coarse index (unchecked-byte (Math/round value)))
      (let [^bytes fine (aget buffers (int (.-fineUniverse channel)))]
        (aset coarse index (unchecked-byte (int value)))
        (aset fine (int (.-fineIndex channel))
                   (unchecked-byte (Math/round (* 255.0 (- value (int value))))))))))

(defn- create-compact [patch]
  (let [count (count (:fixtures patch))
        fields (cond-> compact-specs (contains? (::attribute-slots patch) :shutter) (conj [:shutter :number 1]))
        arrays (object-array (map (fn [[_ _ components]] (double-array (* count components))) fields))
        masks (object-array (map (fn [_] (boolean-array count)) fields))]
    {:arrays arrays :masks masks
     :view {:count count :target-order (:target-order patch)
            :fields (into {} (map-indexed (fn [index [attribute type components]]
                                           [attribute {:type type :components components
                                                       :values (aget arrays index) :valid (aget masks index)}]) fields))}}))

(defn- compact-scalar! [compact field index value]
  (let [^doubles values (aget ^objects (:arrays compact) (int field))
        ^booleans valid (aget ^objects (:masks compact) (int field))]
    (aset-double values (int index) (double value))
    (aset-boolean valid (int index) true)))

(defn- compact-vector! [compact field index value]
  (let [^doubles values (aget ^objects (:arrays compact) (int field))
        ^booleans valid (aget ^objects (:masks compact) (int field))
        base (* (int index) 3)]
    (dotimes [component 3] (aset-double values (+ base component) (double (nth value component))))
    (aset-boolean valid (int index) true)))

(defn- prepare-previous-compact [patch options]
  (if-let [compact (:previous-compact options)]
    (let [n (:count compact), ids (:target-order compact)]
      (when-not (and (map? compact) (integer? n) (not (neg? n))
                     (vector? ids) (= n (count ids)) (map? (:fields compact)))
        (fail! "Invalid previous compact frame" {}))
      (doseq [attribute [:pan :tilt]
              :let [{:keys [values valid type components]} (get-in compact [:fields attribute])]]
        (when-not (and (= type :number) (= components 1)
                       (= (class values) (class (double-array 0)))
                       (= (class valid) (class (boolean-array 0)))
                       (= n (alength ^doubles values)) (= n (alength ^booleans valid)))
          (fail! "Invalid previous compact movement field" {:attribute attribute})))
      (cond-> options
        (not= ids (:target-order patch)) (assoc ::previous-indices (zipmap ids (range)))))
    options))

(defn- previous-for-target [options fixture]
  (let [id (:id fixture), history (get (:previous-values options) id {})
        ;; Rich output omits unauthored top-level axes, but still packs their
        ;; channel defaults. A new aim must choose its wrap from those physical
        ;; values, just as compact history does after a zero-opacity frame.
        previous (reduce (fn [values axis]
                           (if (or (contains? values axis) (not (contains? (:channels history) axis))) values
                               (assoc values axis (get-in history [:channels axis])))) history [:pan :tilt])]
    (if-let [compact (:previous-compact options)]
      (let [index (if-let [indices (::previous-indices options)] (get indices id) (::index fixture))]
        (if (nil? index) previous
            (reduce (fn [result attribute]
                      (let [{:keys [values valid]} (get-in compact [:fields attribute])]
                        (if (or (contains? result attribute) (not (aget ^booleans valid (int index)))) result
                            (assoc result attribute (aget ^doubles values (int index)))))) previous [:pan :tilt])))
      previous)))

(defn previous-pans
  "Read the last accepted normalized pan by stable fixture ID, in the requested
  order. Accepts the same :previous-values and :previous-compact as resolve-frame.
  A nil entry directs a solver to use the fixture's neutral calibration."
  [patch target-ids options]
  (when-not (map? (:previous-values options {}))
    (fail! "Previous values must be a map keyed by fixture ID" {}))
  (let [history (prepare-previous-compact patch options)]
    (mapv (fn [id]
            (let [fixture (or (get (:by-id patch) id) (fail! "Unknown movement target" {:fixture-id id}))
                  pan (:pan (previous-for-target history fixture))]
              (when (and (some? pan) (not (unit? pan)))
                (fail! "Previous pan must be a normalized finite value" {:fixture-id id :pan pan}))
              pan))
          target-ids)))

(defn- write-emitter-tints!
  "Add named emitters to RGBW before gamut limiting and the common dimmer.
  The same compiled spectral weights serve general and dense frames."
  [tints assigned ^doubles values base ^doubles out offset red green blue intensity]
  (loop [i 0, r (double red), g (double green), b (double blue)]
    (if (= i (count tints))
      (do
        (aset-double out (int offset) (* (double intensity) (min 1.0 r)))
        (aset-double out (inc (int offset)) (* (double intensity) (min 1.0 g)))
        (aset-double out (+ 2 (int offset)) (* (double intensity) (min 1.0 b)))
        out)
      (let [^EmitterTint tint (nth tints i)
            level (if values (aget values (+ (int base) (.-slot tint)))
                      (double (get assigned (.-attribute tint) 0.0)))]
        (recur (inc i) (+ r (* level (.-red tint))) (+ g (* level (.-green tint))) (+ b (* level (.-blue tint))))))))

(defn- pack-target! [fixture assigned {:keys [master blackout? include-values?] :as options} universes indexed compact]
  (let [id (:id fixture)
        source (when-let [^objects sources (::geometry-sources options)]
                 (get (aget sources (int (::index fixture))) (if (:aim assigned) :aim :direction)))
        previous (previous-for-target options fixture)
        assigned (if-let [solved (get (::solved-movement options) id)]
                   (apply-solved-geometry fixture assigned previous solved source)
                   (resolve-geometry fixture assigned previous source))
        color (:color assigned [0.0 0.0 0.0])
        has-emitters? (::emitter? fixture)
        dimmer (:dimmer assigned (if has-emitters? 1.0 0.0))
        intensity (if blackout? 0.0 (* master dimmer))
        extracted (if (= :extract-min (:rgbw-policy fixture)) (apply min color) 0.0)
        red (get assigned :red (- (nth color 0) extracted))
        green (get assigned :green (- (nth color 1) extracted))
        blue (get assigned :blue (- (nth color 2) extracted))
        white (get assigned :white extracted)
        ;; Devices with a real dimmer apply intensity there; RGB-only devices
        ;; require scaling emitter channels. Blackout zeros both paths.
        scale (if (and (not blackout?) (::dimmer? fixture)) 1.0 intensity)
        channel-values (reduce-kv
                        (fn [values attribute channel]
                          (let [fog-idle? (and (::fog-off channel)
                                               (or blackout? (zero? master) (not (contains? assigned :fog))))
                                value (case attribute
                                        :fog (if fog-idle? (::fog-idle-level channel) (get assigned :fog 0.0))
                                        :dimmer intensity
                                        :red (* scale red) :green (* scale green)
                                        :blue (* scale blue) :white (* scale white)
                                        (let [raw (get assigned attribute 0.0)]
                                          (if (contains? extra-emitters attribute) (* scale raw) raw)))]
                            (if fog-idle?
                              (write-off-bytes! universes (::fog-off channel))
                              (if-let [scatter (::scatter channel)] (pack-scatter! indexed scatter (double value))
                                      (pack-value! universes channel value)))
                            (when (and compact (some? (::compact-index channel)))
                              (compact-scalar! compact (::compact-index channel) (::index fixture) value))
                            (if include-values? (assoc! values attribute value) values)))
                        (when include-values? (transient {})) (:compiled-channels fixture))]
    (when (or include-values? compact)
      (let [emitted-color (cond
                            (and (not has-emitters?) (::dimmer? fixture))
                            (mapv #(* intensity %) (:emission-color fixture [1.0 1.0 1.0]))
                            (seq (::tints fixture))
                            (vec (write-emitter-tints! (::tints fixture) assigned nil 0 (double-array 3) 0
                                                       (+ red white) (+ green white) (+ blue white) intensity))
                            :else [(* intensity (min 1.0 (+ red white)))
                             (* intensity (min 1.0 (+ green white)))
                             (* intensity (min 1.0 (+ blue white)))])
            emitters (when include-values?
                       (reduce-kv (fn [levels attr level]
                                    (if (contains? extra-emitters attr) (assoc levels attr level) levels))
                                  {:red red :green green :blue blue :white white} assigned))]
        (when compact
          (compact-vector! compact 5 (::index fixture) emitted-color)
          (compact-scalar! compact 6 (::index fixture) intensity)
          (when (:aim assigned) (compact-vector! compact 7 (::index fixture) (:aim assigned)))
          (when (:direction assigned) (compact-vector! compact 8 (::index fixture) (:direction assigned))))
        (when include-values?
         (into assigned {:id id :position (:position fixture) :color color :dimmer dimmer
                        :intensity intensity :emitted-color emitted-color
                        :emitter-values emitters :channels (persistent! channel-values)}))))))

(defn- put-byte! [universes [universe index] value]
  (let [^bytes buffer (get universes universe)]
    (aset-byte buffer (int index) (unchecked-byte (int value)))))

(defn pack-value!
  "Write normalized [0,1] channel level to exclusively owned byte arrays.
  This low-level function mutates supplied buffers; resolve-frame creates and
  owns them. Fine channels preserve legacy fractional-255 packing: .5 becomes
  coarse 127/fine 128, 1.0 becomes coarse 255/fine 0."
  [universes {:keys [coarse fine inverted-from]} level]
  (when-not (unit? level) (fail! "Channel level must be finite and within [0,1]" {:value level}))
  (let [value (* 255.0 (double level))
        value (if (and (some? inverted-from) (>= value inverted-from))
                (- 255.0 (- value inverted-from)) value)]
    (if fine
      (do (put-byte! universes coarse (int value))
          (put-byte! universes fine (Math/round (* 255.0 (- value (int value))))))
      (put-byte! universes coarse (Math/round value)))))

(defn- write-packed-assignment!
  [^doubles values ^booleans present index value blend opacity target-id attribute extended?]
  (when (pos? opacity)
   (let [index (int index)
        before (aget values index)
        blended (case blend :replace value :add (+ before value) :max (max before value))
        next-value (double (if (== 1 opacity) blended (+ before (* opacity (- blended before)))))]
    (when-not (if extended? (and (Double/isFinite next-value) (not (neg? next-value))) (unit? next-value))
      (fail! "Blended assignment exceeds its finite attribute range" {:target-id target-id :attribute attribute :value next-value}))
    (aset-double values index next-value)
    (aset-boolean present index true))))

(defn- apply-hdr! [patch options ^doubles values ^booleans present ^objects general]
  (when-let [settings (:hdr options)]
    (let [slots (::attribute-slots patch)
          stride (long (::stride patch))
          rich? (fn [i] (or (nil? values) (and general (some? (aget general (int i))))))
          read-at! (fn [i attr fallback]
                     (if (rich? i) (get (aget general (int i)) attr fallback)
                       (let [base (* (long i) stride)]
                         (if (= attr :color)
                           (if (aget present base) [(aget values base) (aget values (inc base)) (aget values (+ base 2))] fallback)
                           (if-let [slot (slots attr)]
                             (let [at (+ base (long slot))] (if (aget present at) (aget values at) fallback))
                             fallback)))))
          high-at? (fn [head]
                     (let [i (int (:index head))]
                       (if (rich? i)
                         (some (fn [[a v]] (and (hdr/light-attributes a)
                                                (if (= :color a) (some #(> (double %) 1.0) v) (> (double v) 1.0))))
                               (aget general i))
                         (let [base (* i stride) ^ints scan (:scan-slots head)]
                           (loop [j 0]
                             (when (< j (alength scan))
                               (if (> (aget values (+ base (aget scan j))) 1.0) true (recur (inc j)))))))))
          write-at! (fn [i updates]
                      (if (rich? i) (aset general (int i) (merge (aget general (int i)) updates))
                        (let [base (* (long i) stride)]
                          (doseq [[attr v] updates]
                            (if (= attr :color)
                              (dotimes [c 3]
                                (aset values (+ base c) (double (nth v c)))
                                (aset present (+ base c) true))
                              (let [at (+ base (long (slots attr)))]
                                (aset values at (double v)) (aset present at true)))))))]
      (hdr/process! @(::hdr-layout patch) settings read-at! write-at! high-at? (count (:fixtures patch))
                    (when values (packed-hdr/->Storage values present stride general))
                    (and (:observe-hdr? options) (not (:blackout? options)) (pos? (:master options)))))))

(defn- pack-dense-state
  [patch ^doubles values ^booleans present {:keys [master blackout? compact-values?] :as options}]
  (let [stride (int (::stride patch)), master (double master)
        fixtures (::dense-fixtures patch), fixture-count (count fixtures)
        ^objects general (::general-assigned options)
        {:keys [universes indexed]} (create-buffers patch)
        compact (when compact-values? (create-compact patch))
        ^objects compact-arrays (:arrays compact), ^objects compact-masks (:masks compact)
        ^doubles colors (when compact (aget compact-arrays 5))
        ^doubles intensities (when compact (aget compact-arrays 6))]
    (when compact
      (java.util.Arrays/fill ^booleans (aget compact-masks 5) true)
      (java.util.Arrays/fill ^booleans (aget compact-masks 6) true))
    (dotimes [index fixture-count]
      (if-let [assigned (when general (aget general index))]
        (pack-target! (nth (:fixtures patch) index) assigned options universes indexed compact)
        (let [^DenseFixture fixture (nth fixtures index)
              base (* stride index)
              dimmer (if (aget present (+ base 3)) (aget values (+ base 3)) (if (.-emitter fixture) 1.0 0.0))
              intensity (if blackout? 0.0 (* master dimmer))
              extracted (if (.-extractMin fixture)
                          (min (aget values base) (min (aget values (inc base)) (aget values (+ base 2)))) 0.0)
              red (if (aget present (+ base 4)) (aget values (+ base 4)) (- (aget values base) extracted))
              green (if (aget present (+ base 5)) (aget values (+ base 5)) (- (aget values (inc base)) extracted))
              blue (if (aget present (+ base 6)) (aget values (+ base 6)) (- (aget values (+ base 2)) extracted))
              white (if (aget present (+ base 7)) (aget values (+ base 7)) extracted)
              scale (if (and (not blackout?) (.-dimmer fixture)) 1.0 intensity)
              channels (.-channels fixture)]
          (dotimes [channel-index (count channels)]
            (let [^DenseChannel channel (nth channels channel-index)
                  kind (.-kind channel)
                  fog-idle? (and (== 7 kind) (or blackout? (zero? master)
                                                  (not (aget present (+ base (.-slot channel))))))
                  level (case kind
                          0 intensity 1 (* scale red) 2 (* scale green)
                          3 (* scale blue) 4 (* scale white)
                          5 (* scale (aget values (+ base (.-slot channel))))
                          (aget values (+ base (.-slot channel))))
                  scatter (.-scatter channel), compact-index (.-compactIndex channel)]
              (if fog-idle?
                (write-off-bytes! universes (::fog-off (.-fallback channel)))
                (if scatter (pack-scatter! indexed scatter level)
                    (pack-value! universes (.-fallback channel) level)))
              (when (and compact (>= compact-index 0))
                (aset ^doubles (aget compact-arrays (int compact-index)) index level)
                (aset ^booleans (aget compact-masks (int compact-index)) index true))))
          (when compact
            (aset intensities index intensity)
            (let [color-base (* index 3)]
              (cond
                (and (not (.-emitter fixture)) (.-dimmer fixture))
                (let [emission (.-emission fixture)]
                  (dotimes [component 3]
                    (aset colors (+ color-base component) (* intensity (double (nth emission component))))))
                (seq (.-tints fixture))
                (write-emitter-tints! (.-tints fixture) nil values base colors color-base
                                      (+ red white) (+ green white) (+ blue white) intensity)
                :else
                (do (aset colors color-base (* intensity (min 1.0 (+ red white))))
                    (aset colors (inc color-base) (* intensity (min 1.0 (+ green white))))
                    (aset colors (+ color-base 2) (* intensity (min 1.0 (+ blue white)))))))))))
    (cond-> {:values nil :universes universes :target-order (:target-order patch)}
      compact (assoc :compact (:view compact)))))

(defn- resolve-packed-only
  "Fast transport path for scalar/color frames. Scratch storage is owned by
  this call; geometric/exact-number frames keep the general numeric path."
  [patch assignments options]
  (let [stride (int (::stride patch))
        slots (::attribute-slots patch)
        count (* stride (count (:fixtures patch)))
        values (double-array count)
        present (boolean-array count)
        by-id (:by-id patch)]
    (doseq [{:keys [target-id attribute value blend opacity] :or {blend :replace opacity 1} :as assignment} assignments]
      (let [fixture (get by-id target-id)]
        (validate-assignment! fixture target-id attribute value blend assignment (::hdr? patch))
        (let [base (* stride (int (::index fixture)))]
          (if (= :color attribute)
            (dotimes [component 3]
              (write-packed-assignment! values present (+ base component) (nth value component)
                                        blend opacity target-id attribute (and (::hdr? patch) (::emission-channels fixture) (hdr/light-attributes attribute))))
            (write-packed-assignment! values present (+ base (int (get slots attribute))) value
                                      blend opacity target-id attribute (and (::hdr? patch) (::emission-channels fixture) (hdr/light-attributes attribute)))))))
    (pack-dense-state patch values present options)))

(defn- packed-assignment? [assignment]
  (and (not (geometric-attributes (:attribute assignment)))
       (packed-number? (:opacity assignment 1))
       (let [value (:value assignment)]
         (if (vector? value) (every? packed-number? value) (packed-number? value)))))

(defn- packed-plan? [patch]
  ;; A highly heterogeneous rig should not allocate target-count × every unique
  ;; channel attribute. Fall back to sparse maps before scratch grows unbounded.
  (and (<= (::stride patch) 64)
       (<= (* (long (::stride patch)) (count (:fixtures patch))) 4000000)))

(defn- pack-general-state [patch ^objects assigned options]
  (let [options (prepare-previous-compact patch options)
        {:keys [universes indexed]} (create-buffers patch)
        compact (when (:compact-values? options) (create-compact patch))
        values (reduce (fn [values fixture]
                         (let [resolved (pack-target! fixture (or (aget assigned (int (::index fixture))) {})
                                                      options universes indexed compact)]
                           (if (:include-values? options) (assoc! values (:id fixture) resolved) values)))
                       (when (:include-values? options) (transient {})) (:fixtures patch))]
    (cond-> {:values (when values (persistent! values)) :universes universes :target-order (:target-order patch)}
      compact (assoc :compact (:view compact)))))

(declare resolve-contributions)

(defn resolve-frame
  "Resolve an ordered assignment vector to per-target values and fresh DMX bytes.

  First argument is a fixture vector or immutable compile-patch result. Options:
  :master [0,1] (default 1), :blackout? (default false), :previous-values for aim
  continuity, or :previous-compact to read pan/tilt history directly from typed
  fields. History remaps by stable ID when target order changes, without full UI
  projection. Returned :target-order preserves fixture order. :values includes
  logical attributes, final :channels, and :emitted-color for preview. No buffer
  aliases an earlier call. :include-values? false omits rich preview maps,
  returning :values nil, while producing identical bytes. :compact-values? true
  adds owned typed fields with validity masks for emitted color, intensity,
  pan/tilt, focus/zoom/strobe, aim and direction. Computation runs once; callers
  may request compact projection only on frames they intend to publish.
  Invalid calls return no frame.

  RGBW extraction is explicit. Basic yaw/elevation calibration does not model all
  moving-head kinematics, function channels, dimmer curves or photometry."
  ([fixtures assignments] (resolve-frame fixtures assignments {}))
  ([fixtures assignments options]
   (let [patch (if (and (map? fixtures) (= ::patch (:type fixtures))) fixtures (compile-patch fixtures))
         options (merge {:master 1.0 :blackout? false :previous-values {} :include-values? true :compact-values? false} options)]
     (when-not (and (unit? (:master options)) (instance? Boolean (:blackout? options))
                    (instance? Boolean (:include-values? options)) (instance? Boolean (:compact-values? options))
                    (map? (:previous-values options)))
       (fail! "Invalid render options" {:options options}))
     (when-not (vector? assignments) (fail! "Assignments must be a vector" {}))
     (cond
       (or (:hdr options) (:observe-hdr? options) (seq (:edge-tracking options)))
       (resolve-contributions patch [{:kind :assignments :assignments assignments}] options)

       (and (not (:include-values? options)) (packed-plan? patch) (packed-number? (:master options))
            (every? packed-assignment? assignments))
       (resolve-packed-only patch assignments options)

       :else (pack-general-state patch (reduce-assignments patch assignments) options)))))

(defn- compact-view! [compact]
  (when-not (and (map? compact) (integer? (:count compact)) (not (neg? (:count compact)))
                 (vector? (:target-order compact)) (map? (:fields compact)))
    (fail! "Expected a compact frame projection" {}))
  compact)

(defn- compact-value [^doubles values n index]
  (if (= n 1)
    (aget values (int index))
    (let [offset (int (* index n))]
      (if (= n 3)
        [(aget values offset) (aget values (inc offset)) (aget values (+ offset 2))]
        (mapv #(aget values (+ offset %)) (range n))))))

(defn- compact-row [order fields index]
  (reduce-kv (fn [row attribute {:keys [components values valid]}]
               (if (aget ^booleans valid (int index))
                 (assoc row attribute (compact-value values components index))
                 row))
             {:id (nth order index)} fields))

(defn project-compact
  "Project selected stable target indices from a completed compact frame.
  Returns ordinary maps for UI consumers without evaluating effects or packing
  output again. Omitted fields have a false validity mask. Pass a small visible
  selection or call at a lower UI rate; omit indices to project every target."
  ([compact] (project-compact compact (range (:count compact))))
  ([compact indices]
   (compact-view! compact)
   (mapv (fn [index]
           (when-not (and (integer? index) (<= 0 index) (< index (:count compact)))
             (fail! "Compact projection target index is out of range" {:index index}))
           (compact-row (:target-order compact) (:fields compact) index))
         indices)))

(defn compact-index
  "Prepare a target-ID index once for frames with this target order."
  [order]
  {:order order :indices (zipmap order (range))})

(defn compact-reader
  "Create an ID -> row reader for attributes in one completed frame. A published
  row is shared by subsequent lookups, including concurrent requests. Missing
  targets return nil. Discard the reader when the frame is no longer needed."
  [{:keys [order indices]} compact attributes]
  (compact-view! compact)
  (when-not (or (identical? order (:target-order compact)) (= order (:target-order compact)))
    (fail! "Rebuild the compact index when the fixture order changes" {}))
  (let [rows (java.util.concurrent.atomic.AtomicReferenceArray. (int (:count compact)))
        fields (select-keys (:fields compact) attributes)]
    (fn [id]
      (when-some [index (get indices id)]
        (or (.get rows (int index))
            (let [row (compact-row order fields index)]
              (if (.compareAndSet rows (int index) nil row) row (.get rows (int index)))))))))

(def ^:private doubles-class (class (double-array 0)))

(defn- ordered-prefix-length [ids target-order]
  (let [limit (min (count ids) (count target-order))]
    (loop [row 0]
      (if (and (< row limit) (= (nth ids row) (nth target-order row)))
        (recur (inc row))
        row))))

(defn- fixture-index [by-id id]
  (if-let [fixture (get by-id id)]
    (::index fixture)
    (fail! "Unknown batch target" {:target-id id})))

(defn- batch-target-indices
  "A nil index means each batch row already addresses its patch row. This
  includes ordered prefixes (e.g. all strip pixels before the moving heads)."
  [{:keys [target-order by-id]} ids]
  (when-not (identical? ids target-order)
    (let [n (count ids)
          prefix (long (ordered-prefix-length ids target-order))]
      (when (< prefix n)
        (let [indices (int-array n)]
          (dotimes [row n]
            (aset indices row (int (if (< row prefix) row (fixture-index by-id (nth ids row))))))
          indices)))))

(defn- validate-batches [patch batches & [layer?]]
  (when-not (vector? batches) (fail! "Batches must be an ordered vector" {}))
  (mapv
   (fn [{:keys [target-ids outputs blend count opacity] :or {blend :replace opacity 1} :as batch}]
     (when-not (and (map? batch) (vector? target-ids) (map? outputs) (seq outputs)
                    (#{:replace :max :add} blend) (unit? opacity) (or (nil? count) (= count (clojure.core/count target-ids))))
       (fail! "Invalid batch shape, count or blend" {}))
     (let [target-indices (batch-target-indices patch target-ids)
           columns (mapv
                    (fn [[attribute {:keys [type components values]}]]
                      (let [vector? (or (= :color attribute) (geometric-attributes attribute))
                            expected-width (if vector? 3 1)
                            expected-type (if vector? :vec3 :number)]
                        (when-not (and (keyword? attribute) (= components expected-width) (= type expected-type)
                                       (instance? doubles-class values)
                                       (= (alength ^doubles values) (* expected-width (clojure.core/count target-ids))))
                          (fail! "Invalid typed batch output field" {:attribute attribute}))
                        (when (and (geometric-attributes attribute) (not= :replace blend))
                          (fail! "Geometry assignments require :replace blend" {:attribute attribute}))
                        (when-not (or (and layer? (= :beat-ratio attribute))
                                      (contains? (::common-attributes patch) attribute))
                          (doseq [id target-ids]
                            (when-not (contains? (::supported (get (:by-id patch) id)) attribute)
                              (fail! "Fixture does not implement batch attribute" {:target-id id :attribute attribute}))))
                        {:attribute attribute :components components :values values
                         :slot (if (= attribute :color) 0 (get (::attribute-slots patch) attribute))}))
                    (sort-by (comp str key) outputs))]
       {:target-ids target-ids :target-indices target-indices :columns columns :blend blend :opacity opacity})) batches))

(defn- validate-covered-prefix!
  [patch attribute high? ^doubles source width length ^booleans excluded]
  ;; These opaque inputs cannot contribute to the final column. A hidden
  ;; invalid value must still fault its source in the original row order.
  (let [width (long width)]
    (dotimes [row (long length)]
      (when-not (and excluded (aget excluded row))
        (let [allow-hdr? (and high? (or (not= :dimmer attribute)
                                        (::emission-channels (nth (:fixtures patch) row))))]
          (dotimes [component width]
            (let [v (aget source (+ (* row width) component))]
              (when-not (and (Double/isFinite v) (<= 0.0 v) (or allow-hdr? (<= v 1.0)))
                (fail! "Typed batch value must be finite and within [0,1]"
                       {:attribute attribute :row row :value v})))))))))

(defn- merge-packed-batches!
  ([patch target-values target-present batches]
   (merge-packed-batches! patch target-values target-present batches nil))
  ([patch ^doubles target-values ^booleans target-present batches ^booleans excluded]
   (let [stride (int (::stride patch))]
     (doseq [{:keys [target-ids target-indices columns blend opacity ::layers/opacities]} batches
             {:keys [attribute components values slot] :as column} columns]
       (let [^doubles source values, row-count (count target-ids), components (int components)
             opacity (double opacity)
             skip (long (::coverage/validate-prefix column 0))
             high? (and (::hdr? patch) (hdr/light-attributes attribute))]
         (when (pos? skip)
           (validate-covered-prefix! patch attribute high? source components skip excluded))
         (dotimes [offset (- row-count skip)]
           (let [row (+ skip offset)
                 index (long (if target-indices (aget ^ints target-indices row) row))
                 base (* index stride)
                 opacity (if opacities (aget ^doubles opacities row) opacity)]
             (when-not (or (and opacities (zero? opacity)) (and excluded (aget excluded (int index))))
               (dotimes [component components]
                 (let [value (aget source (+ (* row components) component))
                       permitted? (and high? (or (not= :dimmer attribute)
                                                  (::emission-channels (nth (:fixtures patch) index))))]
                   (when-not (and (Double/isFinite value) (<= 0.0 value) (or permitted? (<= value 1.0)))
                     (fail! "Typed batch value must be finite and within [0,1]" {:attribute attribute :row row :value value}))
                   (let [destination (+ base (int slot) component)
                         before (aget target-values destination)
                         blended (case blend :replace value :add (+ before value) :max (max before value))
                         level (if (== 1.0 opacity) blended (+ before (* opacity (- blended before))))]
                     (when-not (and (Double/isFinite level) (<= 0.0 level) (or permitted? (<= level 1.0)))
                       (fail! "Blended assignment exceeds its finite attribute range"
                              {:target-id (nth target-ids row) :attribute attribute :value level}))
                     (when (pos? opacity)
                       (aset target-values destination level)
                       (aset target-present destination true)))))))))))))

(defn- merge-packed-assignments!
  [patch ^doubles values ^booleans present assignments]
  (let [stride (int (::stride patch)), slots (::attribute-slots patch), by-id (:by-id patch)]
    (doseq [{:keys [target-id attribute value blend opacity] :or {blend :replace opacity 1} :as assignment} assignments]
      (let [fixture (get by-id target-id)]
        (validate-assignment! fixture target-id attribute value blend assignment (::hdr? patch))
        (let [base (* stride (int (::index fixture)))]
          (if (= :color attribute)
            (dotimes [component 3]
              (write-packed-assignment! values present (+ base component) (nth value component)
                                        blend opacity target-id attribute (and (::hdr? patch) (::emission-channels fixture) (hdr/light-attributes attribute))))
            (write-packed-assignment! values present (+ base (int (get slots attribute))) value
                                      blend opacity target-id attribute (and (::hdr? patch) (::emission-channels fixture) (hdr/light-attributes attribute)))))))))

(defn- expand-batch
  ([batch] (expand-batch batch nil))
  ([{:keys [target-ids columns blend opacity ::layers/opacities]} selected]
   (for [row (range (count target-ids))
         :let [id (nth target-ids row)]
         :when (and (or (nil? selected) (contains? selected id))
                    (or (nil? opacities) (pos? (aget ^doubles opacities row))))
         {:keys [attribute components values]} columns]
     {:target-id id :attribute attribute :blend blend :opacity (if opacities (aget ^doubles opacities row) opacity)
      :value (if (= 1 components) (aget ^doubles values row)
                 (mapv #(aget ^doubles values (+ (* row components) %)) (range components)))})))

(defn- layer-rows [block targets]
  (case (:kind block)
    :batch (expand-batch (:compiled block) targets)
    :assignments (if targets (filter #(contains? targets (:target-id %)) (:assignments block))
                     (:assignments block))))

(defn- general-targets
  "A target's entire ordered history must retain general arithmetic when any
  write uses geometry or exact numbers. Other targets stay in dense storage."
  [blocks]
  (reduce (fn [targets block]
            (case (:kind block)
              :assignments (into targets (keep #(when-not (packed-assignment? %) (:target-id %)))
                                 (:assignments block))
              :batch (let [{:keys [target-ids columns opacity]} (:compiled block)]
                       (if (or (not (packed-number? opacity))
                               (some #(geometric-attributes (:attribute %)) columns))
                         (into targets target-ids) targets)))) #{} blocks))

(defn- expand-general-rows [{:keys [target-ids target-indices columns blend opacity ::layers/opacities]} ^booleans general]
  ;; A large pixel batch may have only a few geometric targets. Scan the mask
  ;; with a primitive index, retaining only selected row indices. Assignment
  ;; maps remain streamed in row order, including repeated/reordered IDs.
  (let [row-count (count target-ids)
        rows (loop [row 0, selected (transient [])]
               (if (< row row-count)
                 (recur (inc row)
                        (if (and (aget general (int (if target-indices (aget ^ints target-indices row) row)))
                                 (or (nil? opacities) (pos? (aget ^doubles opacities row))))
                          (conj! selected row) selected))
                 (persistent! selected)))]
    (for [row rows, {:keys [attribute components values]} columns]
      {:target-id (nth target-ids row) :attribute attribute :blend blend :opacity (if opacities (aget ^doubles opacities row) opacity)
       :value (if (= 1 components) (aget ^doubles values row)
                  (mapv #(aget ^doubles values (+ (* row components) %)) (range components)))})))

(defn- geometry-source-storage [patch blocks]
  (when (some #(some? (:source %)) blocks)
    (object-array (count (:fixtures patch)))))

(defn- tracking-ids [links]
  (into #{} (mapcat (juxt :leader :follower)) links))

(defn- track-edge [patch ^objects assigned options {:keys [leader follower surface along]}]
  (let [head (get (:by-id patch) leader)
        next-head (get (:by-id patch) follower)]
    (cond
      (nil? head) {:reason :missing-leader}
      (nil? next-head) {:reason :missing-follower}
      (not (contains? (::supported next-head) :aim)) {:reason :fixed-follower}
      :else
      (let [index (int (::index head))
            attrs (aget assigned index)
            sources (::geometry-sources options)
            source (when sources (get (aget ^objects sources index) (if (:aim attrs) :aim :direction)))
            resolved (resolve-geometry head attrs (previous-for-target options head) source)
            ;; Absent direct axes pack channel value zero, exactly as in the
            ;; completed frame. Reconstruct travel limits from the command.
            pose (fixture-pose head (merge {:pan 0.0 :tilt 0.0} resolved))
            spot (optics/beam-footprint (optics/fixture-beam head (assoc resolved :pose pose)) surface)
            next-attrs (aget assigned (int (::index next-head)))
            follower-beam (optics/fixture-beam next-head next-attrs)]
        (if-let [solution (when spot (optics/edge-aim spot follower-beam surface along))]
          (let [target (assoc next-attrs :aim (:aim solution))
                calibrated (resolve-geometry next-head target (previous-for-target options next-head) nil)]
            (if (:aim-reachable? calibrated)
              (select-keys solution [:aim :contact])
              {:reason :unreachable}))
          {:reason (if spot :no-tangent :missed-receiver)})))))

(defn- apply-tracking! [patch ^objects assigned options]
  (let [links (:edge-tracking options)]
    (when-not (vector? links) (fail! "Edge tracking must be an ordered vector" {}))
    (loop [pending (seq links), seen #{}, suppressed #{}, reports []]
      (if (seq pending)
        (let [{:keys [leader follower] :as link} (first pending)]
          (when (or (nil? leader) (nil? follower) (= leader follower) (contains? seen follower))
            (fail! "Each follower must be new and distinct from its leader" {:link link}))
          (let [result (if (contains? suppressed leader)
                         {:reason :leader-suppressed}
                         (track-edge patch assigned options link))
                failed? (contains? result :reason)]
            (when-let [fixture (get (:by-id patch) follower)]
              (let [index (int (::index fixture))
                    attrs (aget assigned index)]
                (aset assigned index (if failed? (assoc attrs :dimmer 0.0) (assoc attrs :aim (:aim result))))))
            (recur (next pending) (conj seen leader follower)
                   (cond-> suppressed failed? (conj follower))
                   (conj reports (merge {:leader leader :follower follower} result)))))
        reports))))

(defn- finish-contributions [patch ^objects assigned options values present pack]
  (let [links (:edge-tracking options)
        reports (when (seq links) (apply-tracking! patch assigned (prepare-previous-compact patch options)))
        contacts (when (:hdr options) (apply-hdr! patch options values present assigned))
        _ (when (:hdr options)
            ;; A tracked head that cannot reach its receiver stays dark even
            ;; when a neighboring source sends it HDR spill. Its own dimmer
            ;; was already zero while computing outgoing spatial highlights.
            (doseq [{:keys [follower reason]} reports :when reason
                    :let [i (get-in patch [:by-id follower ::index])] :when (some? i)]
              (aset assigned (int i) (assoc (aget assigned (int i)) :dimmer 0.0))))
        pack (if (or reports (:observe-hdr? options))
               (fn [opts] (cond-> (pack opts)
                            reports (assoc :edge-tracking reports)
                            (:observe-hdr? options) (assoc :hdr-contacts (or contacts {}))))
               pack)]
    (if (::prepare-movement? options)
      (let [targets (if assigned
                      (into {} (keep (fn [fixture]
                                       (let [attributes (aget assigned (int (::index fixture)))]
                                         (cond (:aim attributes) [(:id fixture) {:aim (:aim attributes)}]
                                               (:direction attributes) [(:id fixture) {:direction (:direction attributes)}]))))
                            (::moving-heads patch))
                      {})
            ;; Both sides of a tangent use the same CPU geometry. Independent
            ;; heads may still use the native solver within this frame.
            reference-ids (when reports (tracking-ids links))]
        {:targets targets :reference-ids reference-ids
         :pack (fn [solved]
                 (when-not (and (map? solved) (every? #(and (contains? targets %) (not (contains? reference-ids %))) (keys solved)))
                   (fail! "Movement results do not belong to this frame's eligible heads" {}))
                 (pack (assoc options ::solved-movement solved)))})
      (pack options))))

(defn- resolve-general-contributions [patch blocks options]
  (let [assigned (object-array (count (:fixtures patch)))
        sources (geometry-source-storage patch blocks)]
    (doseq [block blocks]
      (with-effect-source (:source block)
        (merge-general-assignments! patch assigned
                                   (case (:kind block)
                                     :assignments (:assignments block)
                                     :batch (expand-batch (:compiled block)))
                                   sources (:source block))))
    (persist-assignments! assigned)
    (finish-contributions patch assigned (assoc options ::geometry-sources sources) nil nil
                          #(pack-general-state patch assigned %))))

(defn- resolve-partitioned
  [patch blocks options]
  (let [blocks (if (> (count blocks) 1) (coverage/plan blocks) blocks)
        size (* (int (::stride patch)) (count (:fixtures patch)))
        values (double-array size), present (boolean-array size)
        targets (cond-> (general-targets blocks) (seq (:edge-tracking options)) (into (tracking-ids (:edge-tracking options))))]
    (if (empty? targets)
      (do (doseq [block blocks]
            (with-effect-source (:source block)
              (case (:kind block)
                :assignments (merge-packed-assignments! patch values present (:assignments block))
                :batch (merge-packed-batches! patch values present [(:compiled block)]))))
          (finish-contributions patch nil options values present #(pack-dense-state patch values present %)))
      (let [general (boolean-array (count (:fixtures patch)))
            assigned (object-array (count (:fixtures patch)))
            sources (geometry-source-storage patch blocks)]
        (doseq [id targets :let [fixture (get (:by-id patch) id)] :when fixture]
          (aset-boolean general (int (::index fixture)) true))
        (doseq [block blocks]
          (with-effect-source (:source block)
            (case (:kind block)
              :assignments
              (let [groups (group-by #(contains? targets (:target-id %)) (:assignments block))]
                (merge-packed-assignments! patch values present (get groups false))
                (merge-general-assignments! patch assigned (get groups true) sources (:source block)))
              :batch
              (do (merge-packed-batches! patch values present [(:compiled block)] general)
                  (merge-general-assignments! patch assigned (expand-general-rows (:compiled block) general)
                                             sources (:source block))))))
        (persist-assignments! assigned)
        ;; Mark zero-opacity targets too: their absent attributes and history use
        ;; the same reference path. Each target is packed once into private output.
        (dotimes [index (alength general)]
          (when (and (aget general index) (nil? (aget ^objects assigned index)))
            (aset ^objects assigned index {})))
        (finish-contributions patch assigned
                              (assoc (prepare-previous-compact patch options)
                                     ::general-assigned assigned ::geometry-sources sources)
                              values present #(pack-dense-state patch values present %))))))

(defn- reduce-contributions [fixtures contributions options]
  (let [patch (if (and (map? fixtures) (= ::patch (:type fixtures))) fixtures (compile-patch fixtures))
        options (merge {:master 1.0 :blackout? false :previous-values {} :include-values? true :compact-values? false} options)
        options (cond
                  (:hdr options) options
                  (some :emission-gain contributions) (assoc options :hdr {:white-mix 1.0})
                  (:observe-hdr? options) (assoc options :hdr {})
                  :else options)
        patch (if (:hdr options) (assoc patch ::hdr? true) patch)]
    (when-not (and (unit? (:master options)) (instance? Boolean (:blackout? options))
                   (instance? Boolean (:include-values? options)) (instance? Boolean (:compact-values? options))
                   (map? (:previous-values options)))
      (fail! "Invalid render options" {:options options}))
    (when-not (vector? contributions) (fail! "Contributions must be an ordered vector" {}))
    (when (:hdr options) (hdr/validate! (:hdr options)))
    (let [blocks (mapv (fn [block]
                         (when-not (map? block) (fail! "Invalid contribution block" {}))
                         (with-effect-source (:source block)
                           (case (:kind block)
                             :assignments (do (when-not (vector? (:assignments block))
                                                (fail! "Assignment contribution needs a vector" {})) block)
                             :batch (assoc block :compiled (first (validate-batches patch [(:batch block)] (:native-layer block))))
                             (fail! "Unknown contribution kind" {:kind (:kind block)})))) contributions)
          blocks (hdr/apply-contribution-gains blocks (:hdr options) #(get-in patch [:by-id % ::emission-channels]))
          blocks (layers/compose blocks layer-rows blend-value
                                 (fn [{:keys [target-id attribute value] :as a}]
                                   (validate-assignment! (get (:by-id patch) target-id) target-id attribute value
                                                         (:blend a :replace) a (::hdr? patch))) (::hdr? patch))
          partitioned? (and (not (:include-values? options)) (packed-plan? patch) (packed-number? (:master options)))]
      (if partitioned?
        (resolve-partitioned patch blocks options)
        (resolve-general-contributions patch blocks options)))))

(defn resolve-contributions
  "Resolve the kernel's ordered mixed contribution stream exactly once.

  Blocks are {:kind :assignments :assignments [...]} or {:kind :batch :batch ...}.
  Every block keeps its position; ordinary writes between two batches cannot be
  moved ahead of or behind them. Scalar/color transport frames reduce directly
  into one owned target state, then pack once. Targets using geometry or exact
  numbers keep general arithmetic without expanding unrelated pixel batches.
  Heterogeneous patches, exact master levels and rich values use the general path.
  Assignments and batches accept :opacity in [0,1], default 1. Each write is
  previous + opacity * (blend(previous, value) - previous); zero skips the write,
  preserving earlier contributions and absent-attribute defaults. Geometry uses
  the same componentwise interpolation in world coordinates. Opacity never scales
  authored parameters. Scalar channel overrides remain distinct from RGB color.
  Blocks may carry :source provenance. Output validation/blending failures add
  that exact value as :effect-source in ex-data, retaining the original cause
  and data. Final geometric failures identify the last effective positive-opacity
  aim source, or direction source when no aim exists. Later valid replacement is
  allowed. Global patch/options/history errors remain unattributed. Provenance
  stays per block and sparse geometric target; no source maps are copied per pixel.
  Optional :edge-tracking links run after blending. Each {:leader id :follower id
  :surface receiver :along xyz} places the next beam tangent to its leader on the
  receiver. A missed or unreachable spot suppresses that follower's light for
  the frame and the returned :edge-tracking reports its reason.
  Options and ownership match resolve-frame. Typed arrays must remain read-only
  throughout this call; failed validation returns no frame or partial output."
  ([fixtures contributions] (resolve-contributions fixtures contributions {}))
  ([fixtures contributions options]
   (reduce-contributions fixtures contributions (dissoc options ::prepare-movement? ::solved-movement))))

(defn prepare-movement-frame
  "Purely merge ordered contributions once and capture effective world-space movement.
  :targets maps active head IDs to :aim or :direction after all priority/opacity
  layers. Call :pack with calibrated results for this exact frame (normalized
  pan/tilt, requested pan-deg/tilt-deg and aim-reachable?). Omitted heads use
  CPU geometry. Passing {} is the full CPU fallback. Capture the patch, options
  and last committed history together; the returned plan belongs to this frame."
  [patch contributions options]
  (reduce-contributions patch contributions (assoc (dissoc options ::solved-movement) ::prepare-movement? true)))

(defn resolve-batches
  "Resolve ordered typed batches; convenience form of resolve-contributions.
  Each batch carries :target-ids, :outputs from ir/evaluate-batch, optional
  :count and :blend (:replace/:max/:add). Options match resolve-frame."
  ([fixtures batches] (resolve-batches fixtures batches {}))
  ([fixtures batches options]
   (when-not (vector? batches) (fail! "Batches must be an ordered vector" {}))
   (resolve-contributions fixtures (mapv #(hash-map :kind :batch :batch %) batches) options)))


(defn portable-frame
  "Materialize a completed frame for a portable save boundary, never per tick.
  Converts all compact targets to ordinary values, preserving movement history,
  merges any richer values already present, and converts DMX bytes to unsigned
  vectors. No arrays, compilation, effect evaluation or output IO remain."
  [frame]
  (let [compact-values (when (:compact frame)
                         (into {} (map (juxt :id identity)) (project-compact (:compact frame))))
        values (merge {} compact-values (:values frame))
        ids (:target-order frame)]
    (when-not (and (vector? ids) (every? #(contains? values %) ids) (map? (:universes frame)))
      (fail! "Portable frame needs complete rich or compact values" {}))
    {:target-order ids :values values
     :universes (into (sorted-map)
                      (map (fn [[universe buffer]] [universe (mapv #(bit-and 255 %) buffer)]))
                      (:universes frame))}))

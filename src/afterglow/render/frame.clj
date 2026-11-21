(ns afterglow.render.frame
  "Deterministic fixture resolution and owned DMX packing without I/O.

  Inputs use linear RGB and normalized scalar attributes [0,1]. Geometry uses
  metres, +Y up, a local forward direction of +Z, positive yaw toward +X and
  positive elevation toward +Y. This is a new explicit fixture contract, not
  an implementation of all legacy fixture function ranges/optics.")

(def ^:private emitter-attributes #{:red :green :blue :white :amber :uv})
(def ^:private geometric-attributes #{:aim :direction})
(def ^:private rgb-attributes [:red :green :blue])

;; Final fields, no mutable buffers: safe to share between render workers/frames.
(deftype ChannelScatter [^long universe ^long index ^long fineUniverse ^long fineIndex ^double pivot])
(deftype DenseChannel [^long kind ^long slot ^long compactIndex scatter fallback])
(deftype DenseFixture [^boolean emitter ^boolean dimmer ^boolean extractMin emission channels])
(def ^:private compact-specs
  [[:pan :number 1] [:tilt :number 1] [:focus :number 1] [:zoom :number 1] [:strobe :number 1]
   [:emitted-color :vec3 3] [:intensity :number 1] [:aim :vec3 3] [:direction :vec3 3]])
(def ^:private compact-channel-indices {:pan 0 :tilt 1 :focus 2 :zoom 3 :strobe 4})

(defn- packed-number? [value]
  (or (instance? Double value) (instance? Float value) (integer? value)))

(defn- fail! [message data]
  (throw (ex-info message (assoc data :type ::invalid-frame))))

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

(defn compile-patch
  "Validate and compile fixtures to reusable immutable channel scatter metadata.

  Channel offsets are 1-based relative to fixture :address. Crossing address 512
  advances the universe, including fine channels. Channel values are an offset,
  [coarse fine], or {:offset n :fine-offset n :inverted-from 0|1|...255}.
  :rgbw-policy is :none or :extract-min (requires a white channel).
  Optional :rotation-deg is [x y z], applied X then Y then Z.
  Axis calibration is {:min-deg a :max-deg b}, or legacy [center half-circle]
  values in DMX units. Compilation rejects duplicate IDs and channel collisions."
  [fixtures]
  (when-not (vector? fixtures) (fail! "Fixtures must be a vector" {:path [:fixtures]}))
  (when-not (= (count fixtures) (count (set (map :id fixtures))))
    (fail! "Fixture IDs must be unique" {:path [:fixtures]}))
  (let [compiled
        (mapv
         (fn [index fixture]
           (let [{:keys [id position universe address channels calibration]} fixture]
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
    (let [universes (vec (sort (set (map (comp first :slot) slots))))
          universe-indices (zipmap universes (range))
          compiled (mapv
                    (fn [fixture]
                      (update fixture :compiled-channels
                              (fn [channels]
                                (reduce-kv (fn [result attribute channel]
                                             (assoc result attribute (compile-scatter universe-indices attribute channel)))
                                           {} channels))))
                    compiled)
          base-attributes [:dimmer :red :green :blue :white :amber :uv]
          extra-attributes (sort (remove (set base-attributes) (set (mapcat (comp keys :channels) compiled))))
          attribute-slots (zipmap (concat base-attributes extra-attributes) (range 3 (+ 10 (count extra-attributes))))]
      {:type ::patch :fixtures compiled :by-id (into {} (map (juxt :id identity) compiled))
       :target-order (mapv :id compiled) ::attribute-slots attribute-slots
       ::stride (+ 10 (count extra-attributes))
       ::dense-fixtures
       (mapv (fn [fixture]
               (DenseFixture.
                (::emitter? fixture) (::dimmer? fixture) (= :extract-min (:rgbw-policy fixture))
                (:emission-color fixture [1.0 1.0 1.0])
                (mapv (fn [[attribute channel]]
                        (DenseChannel. (long (case attribute :dimmer 0 :red 1 :green 2 :blue 3 :white 4 (:amber :uv) 5 6))
                                       (long (get attribute-slots attribute))
                                       (long (or (::compact-index channel) -1))
                                       (::scatter channel) channel)) (:compiled-channels fixture)))) compiled)
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

(defn- blend-value [previous value blend]
  (let [op (case blend :replace (fn [_ value] value) :max max :add +)]
    (if (vector? value)
      (mapv op (or previous (vec (repeat (count value) 0))) value)
      (op (or previous 0) value))))

(defn- assignment-value? [attribute value]
  (case attribute
    :color (and (vec3? value) (every? unit? value))
    (:aim :direction) (vec3? value)
    (unit? value)))

(defn- validate-assignment! [fixture target-id attribute value blend assignment]
  (when-not (and (map? assignment) fixture
                 (keyword? attribute) (#{:replace :max :add} blend)
                 (assignment-value? attribute value))
    (fail! "Invalid assignment target, attribute, blend or value" {:assignment assignment}))
  (when (and (= attribute :color) (not (::rgb? fixture)))
    (fail! "Color assignment requires red, green and blue channels" {:target-id target-id}))
  (when-not (contains? (::supported fixture) attribute)
    (fail! "Fixture does not implement assigned attribute" {:target-id target-id :attribute attribute}))
  (when (and (contains? geometric-attributes attribute) (not= :replace blend))
    (fail! "Geometry assignments require :replace blend" {:target-id target-id :attribute attribute})))

(defn- reduce-assignments [patch assignments]
  (when-not (vector? assignments) (fail! "Assignments must be a vector" {}))
  ;; Scratch storage is private to this evaluation. Stable target indices avoid
  ;; rebuilding the outer persistent map for every per-pixel contribution.
  (let [targets (object-array (count (:fixtures patch)))
        by-id (:by-id patch)]
   (doseq [{:keys [target-id attribute value blend] :or {blend :replace} :as assignment} assignments]
    (let [fixture (get by-id target-id)]
     (validate-assignment! fixture target-id attribute value blend assignment)
     (let [index (int (::index fixture))
           attributes (or (aget targets index) (transient {}))
           previous (get attributes attribute)
           blended (blend-value previous value blend)]
       (when-not (assignment-value? attribute blended)
         (fail! "Blended assignment exceeds its finite attribute range" {:target-id target-id :attribute attribute :value blended}))
       (aset targets index (assoc! attributes attribute blended)))))
   (dotimes [index (alength targets)]
     (when-let [attributes (aget targets index)]
       (aset targets index (persistent! attributes))))
   targets))

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

(defn- normalized-angle [fixture axis degrees previous]
  (when (and (some? previous) (not (unit? previous)))
    (fail! "Previous pan/tilt must be normalized finite values" {:fixture-id (:id fixture) :axis axis}))
  (let [calibration (get-in fixture [:calibration axis]
                            (if (= axis :pan) {:min-deg -180 :max-deg 180}
                                {:min-deg -90 :max-deg 90}))
        convert (if (vector? calibration)
                  (fn [angle] (/ (+ (first calibration) (* (/ angle 180.0) (second calibration))) 255.0))
                  (fn [angle] (/ (- angle (:min-deg calibration))
                                 (- (:max-deg calibration) (:min-deg calibration)))))
        candidates (if (= axis :pan) (mapv convert [degrees (- degrees 360) (+ degrees 360)]) [(convert degrees)])
        legal (filterv unit? candidates)
        target (or previous (convert 0))
        nearest (first (sort-by #(Math/abs (double (- % target))) (if (seq legal) legal candidates)))]
    {:value (clamp nearest 0 1) :reachable? (boolean (seq legal)) :degrees degrees}))

(defn- resolve-geometry [fixture assigned previous]
  (if-let [direction (cond (:aim assigned) (mapv - (:aim assigned) (:position fixture))
                          (:direction assigned) (:direction assigned))]
    (let [[x y z :as local] (local-direction fixture direction)
          magnitude (Math/sqrt (+ (* x x) (* y y) (* z z)))]
      (when-not (and (finite? magnitude) (pos? magnitude))
        (fail! "Aim/direction must have finite nonzero distance" {:fixture-id (:id fixture)}))
      (when-not (and (contains? (:channels fixture) :pan) (contains? (:channels fixture) :tilt))
        (fail! "Aim/direction requires pan and tilt channels" {:fixture-id (:id fixture)}))
      (let [pan-deg (Math/toDegrees (Math/atan2 x z))
            tilt-deg (Math/toDegrees (Math/atan2 y (Math/sqrt (+ (* x x) (* z z)))))
            pan (normalized-angle fixture :pan pan-deg (:pan previous))
            tilt (normalized-angle fixture :tilt tilt-deg (:tilt previous))]
        ;; Explicit geometric output takes precedence over direct pan/tilt, like
        ;; the legacy kind order. Attributes inside one kind retain input order.
        (assoc assigned :pan (:value pan) :tilt (:value tilt)
               :pan-deg pan-deg :tilt-deg tilt-deg
               :direction (mapv #(/ % magnitude) direction)
               :aim-reachable? (and (:reachable? pan) (:reachable? tilt)))))
    assigned))

(declare pack-value!)

(defn- create-buffers [patch]
  (let [indexed (object-array (map (fn [_] (byte-array 512)) (:universes patch)))]
    {:indexed indexed :universes (into (sorted-map) (map-indexed (fn [i u] [u (aget indexed i)]) (:universes patch)))}))

(defn- pack-scatter! [^objects buffers ^ChannelScatter channel ^double level]
  (let [value (* 255.0 level)
        pivot (.-pivot channel)
        value (if (and (>= pivot 0.0) (>= value pivot)) (- 255.0 (- value pivot)) value)
        ^bytes coarse (aget buffers (int (.-universe channel)))
        index (int (.-index channel))]
    (if (neg? (.-fineUniverse channel))
      (aset-byte coarse index (unchecked-byte (Math/round value)))
      (let [^bytes fine (aget buffers (int (.-fineUniverse channel)))]
        (aset-byte coarse index (unchecked-byte (int value)))
        (aset-byte fine (int (.-fineIndex channel))
                   (unchecked-byte (Math/round (* 255.0 (- value (int value))))))))))

(defn- create-compact [patch]
  (let [count (count (:fixtures patch))
        arrays (object-array (map (fn [[_ _ components]] (double-array (* count components))) compact-specs))
        masks (object-array (map (fn [_] (boolean-array count)) compact-specs))]
    {:arrays arrays :masks masks
     :view {:count count :target-order (:target-order patch)
            :fields (into {} (map-indexed (fn [index [attribute type components]]
                                           [attribute {:type type :components components
                                                       :values (aget arrays index) :valid (aget masks index)}]) compact-specs))}}))

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

(defn- pack-target! [fixture assigned {:keys [master blackout? previous-values include-values?]} universes indexed compact]
  (let [id (:id fixture)
        assigned (resolve-geometry fixture assigned (get previous-values id))
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
                          (let [value (case attribute
                                        :dimmer intensity
                                        :red (* scale red) :green (* scale green)
                                        :blue (* scale blue) :white (* scale white)
                                        (:amber :uv) (* scale (get assigned attribute 0.0))
                                        (get assigned attribute 0.0))]
                            (if-let [scatter (::scatter channel)] (pack-scatter! indexed scatter (double value))
                                    (pack-value! universes channel value))
                            (when (and compact (some? (::compact-index channel)))
                              (compact-scalar! compact (::compact-index channel) (::index fixture) value))
                            (if include-values? (assoc! values attribute value) values)))
                        (when include-values? (transient {})) (:compiled-channels fixture))]
    (when (or include-values? compact)
      (let [emitted-color (if (and (not has-emitters?) (::dimmer? fixture))
                            (mapv #(* intensity %) (:emission-color fixture [1.0 1.0 1.0]))
                            [(* intensity (min 1.0 (+ red white)))
                             (* intensity (min 1.0 (+ green white)))
                             (* intensity (min 1.0 (+ blue white)))])
            emitters (when include-values?
                       (cond-> {:red red :green green :blue blue :white white}
                         (contains? assigned :amber) (assoc :amber (:amber assigned))
                         (contains? assigned :uv) (assoc :uv (:uv assigned))))]
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
  [^doubles values ^booleans present index value blend target-id attribute]
  (let [index (int index)
        before (aget values index)
        next-value (double (case blend :replace value :add (+ before value) :max (max before value)))]
    (when-not (unit? next-value)
      (fail! "Blended assignment exceeds its finite attribute range" {:target-id target-id :attribute attribute :value next-value}))
    (aset-double values index next-value)
    (aset-boolean present index true)))

(defn- pack-dense-state
  [patch ^doubles values ^booleans present {:keys [master blackout? compact-values?]}]
  (let [stride (int (::stride patch)), master (double master)
        fixtures (::dense-fixtures patch), fixture-count (count fixtures)
        {:keys [universes indexed]} (create-buffers patch)
        compact (when compact-values? (create-compact patch))
        ^objects compact-arrays (:arrays compact), ^objects compact-masks (:masks compact)
        ^doubles colors (when compact (aget compact-arrays 5))
        ^doubles intensities (when compact (aget compact-arrays 6))]
    (when compact
      (java.util.Arrays/fill ^booleans (aget compact-masks 5) true)
      (java.util.Arrays/fill ^booleans (aget compact-masks 6) true))
    (dotimes [index fixture-count]
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
                level (case (.-kind channel)
                        0 intensity 1 (* scale red) 2 (* scale green)
                        3 (* scale blue) 4 (* scale white)
                        5 (* scale (aget values (+ base (.-slot channel))))
                        (aget values (+ base (.-slot channel))))
                scatter (.-scatter channel), compact-index (.-compactIndex channel)]
            (if scatter (pack-scatter! indexed scatter level)
                (pack-value! universes (.-fallback channel) level))
            (when (and compact (>= compact-index 0))
              (aset-double ^doubles (aget compact-arrays (int compact-index)) index level)
              (aset-boolean ^booleans (aget compact-masks (int compact-index)) index true))))
        (when compact
          (aset-double intensities index intensity)
          (let [color-base (* index 3)]
            (if (and (not (.-emitter fixture)) (.-dimmer fixture))
              (let [emission (.-emission fixture)]
                (dotimes [component 3]
                  (aset-double colors (+ color-base component) (* intensity (double (nth emission component))))))
              (do (aset-double colors color-base (* intensity (min 1.0 (+ red white))))
                  (aset-double colors (inc color-base) (* intensity (min 1.0 (+ green white))))
                  (aset-double colors (+ color-base 2) (* intensity (min 1.0 (+ blue white))))))))))
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
    (doseq [{:keys [target-id attribute value blend] :or {blend :replace} :as assignment} assignments]
      (let [fixture (get by-id target-id)]
        (validate-assignment! fixture target-id attribute value blend assignment)
        (let [base (* stride (int (::index fixture)))]
          (if (= :color attribute)
            (dotimes [component 3]
              (write-packed-assignment! values present (+ base component) (nth value component)
                                        blend target-id attribute))
            (write-packed-assignment! values present (+ base (int (get slots attribute))) value
                                      blend target-id attribute)))))
    (pack-dense-state patch values present options)))

(defn- packed-assignment? [assignment]
  (and (not (geometric-attributes (:attribute assignment)))
       (let [value (:value assignment)]
         (if (vector? value) (every? packed-number? value) (packed-number? value)))))

(defn- packed-plan? [patch]
  ;; A highly heterogeneous rig should not allocate target-count × every unique
  ;; channel attribute. Fall back to sparse maps before scratch grows unbounded.
  (and (<= (::stride patch) 64)
       (<= (* (long (::stride patch)) (count (:fixtures patch))) 4000000)))

(defn resolve-frame
  "Resolve an ordered assignment vector to per-target values and fresh DMX bytes.

  First argument is a fixture vector or immutable compile-patch result. Options:
  :master [0,1] (default 1), :blackout? (default false), :previous-values for aim
  continuity. Returned :target-order preserves fixture order. :values includes
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
     (if (and (not (:include-values? options)) (packed-plan? patch) (packed-number? (:master options))
              (every? packed-assignment? assignments))
       (resolve-packed-only patch assignments options)
       (let [assigned (reduce-assignments patch assignments)
           {:keys [universes indexed]} (create-buffers patch)
           compact (when (:compact-values? options) (create-compact patch))
           values (reduce (fn [values fixture]
                            (let [resolved (pack-target! fixture (or (aget ^objects assigned (int (::index fixture))) {})
                                                         options universes indexed compact)]
                              (if (:include-values? options) (assoc! values (:id fixture) resolved) values)))
                          (when (:include-values? options) (transient {})) (:fixtures patch))]
       (cond-> {:values (when values (persistent! values)) :universes universes :target-order (:target-order patch)}
         compact (assoc :compact (:view compact))))))))

(defn project-compact
  "Project selected stable target indices from a completed compact frame.
  Returns ordinary maps for UI consumers without evaluating effects or packing
  output again. Omitted fields have a false validity mask. Pass a small visible
  selection or call at a lower UI rate; omit indices to project every target."
  ([compact] (project-compact compact (range (:count compact))))
  ([compact indices]
   (when-not (and (map? compact) (integer? (:count compact)) (not (neg? (:count compact)))
                  (vector? (:target-order compact)) (map? (:fields compact)))
     (fail! "Expected a compact frame projection" {}))
   (mapv (fn [index]
           (when-not (and (integer? index) (<= 0 index) (< index (:count compact)))
             (fail! "Compact projection target index is out of range" {:index index}))
           (reduce-kv
            (fn [result attribute {:keys [components values valid]}]
              (if (aget ^booleans valid (int index))
                (assoc result attribute
                       (if (= components 1) (aget ^doubles values (int index))
                           (mapv #(aget ^doubles values (+ (* index components) %)) (range components))))
                result))
            {:id (nth (:target-order compact) index)} (:fields compact))) indices)))

(def ^:private doubles-class (class (double-array 0)))

(defn- validate-batches [patch batches]
  (when-not (vector? batches) (fail! "Batches must be an ordered vector" {}))
  (mapv
   (fn [{:keys [target-ids outputs blend count] :or {blend :replace} :as batch}]
     (when-not (and (map? batch) (vector? target-ids) (map? outputs) (seq outputs)
                    (#{:replace :max :add} blend) (or (nil? count) (= count (clojure.core/count target-ids))))
       (fail! "Invalid batch shape, count or blend" {}))
     (let [same-order? (= target-ids (:target-order patch))
           target-indices (if same-order? nil
                              (int-array (map (fn [id]
                                                (if-let [fixture (get (:by-id patch) id)] (::index fixture)
                                                        (fail! "Unknown batch target" {:target-id id}))) target-ids)))
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
                        (when-not (contains? (::common-attributes patch) attribute)
                          (doseq [id target-ids]
                            (when-not (contains? (::supported (get (:by-id patch) id)) attribute)
                              (fail! "Fixture does not implement batch attribute" {:target-id id :attribute attribute}))))
                        {:attribute attribute :components components :values values
                         :slot (if (= attribute :color) 0 (get (::attribute-slots patch) attribute))}))
                    (sort-by (comp str key) outputs))]
       {:target-ids target-ids :target-indices target-indices :columns columns :blend blend})) batches))

(defn resolve-batches
  "Resolve ordered typed CPU/GPU numeric batches without rebuilding assignments.

  Each batch contains :target-ids, :outputs from ir/evaluate-batch, optional
  :count and :blend (:replace/:max/:add). Output arrays must remain read-only for
  this call. All data is validated and merged in batch/row order.

  Rendering options match resolve-frame. Use :include-values? false for the
  dense transport path, optionally :compact-values? true. Rich-map projection,
  geometry and heterogeneous rigs retain the general path. The dense path avoids
  one assignment map per head/attribute; it still performs validated CPU fixture
  resolution and channel packing, and does not submit GPU work."
  ([fixtures batches] (resolve-batches fixtures batches {}))
  ([fixtures batches options]
   (let [patch (if (and (map? fixtures) (= ::patch (:type fixtures))) fixtures (compile-patch fixtures))
         options (merge {:master 1.0 :blackout? false :previous-values {} :include-values? true :compact-values? false} options)
         batches (validate-batches patch batches)
         geometry? (some (fn [batch] (some #(geometric-attributes (:attribute %)) (:columns batch))) batches)]
     (when-not (and (unit? (:master options)) (instance? Boolean (:blackout? options))
                    (instance? Boolean (:include-values? options)) (instance? Boolean (:compact-values? options))
                    (map? (:previous-values options)))
       (fail! "Invalid render options" {:options options}))
     (if (and (not (:include-values? options)) (not geometry?) (packed-plan? patch) (packed-number? (:master options)))
       (let [stride (int (::stride patch))
             size (* stride (count (:fixtures patch)))
             target-values (double-array size)
             target-present (boolean-array size)]
         (doseq [{:keys [target-ids target-indices columns blend]} batches
                 {:keys [attribute components values slot]} columns]
           (let [^doubles source values, row-count (count target-ids), components (int components)]
             (dotimes [row row-count]
               (let [index (long (if target-indices (aget ^ints target-indices row) row))
                     base (+ (* index stride) (int slot))]
                 (dotimes [component components]
                   (let [value (aget source (+ (* row components) component))]
                     (when-not (and (Double/isFinite value) (<= 0.0 value) (<= value 1.0))
                       (fail! "Typed batch value must be finite and within [0,1]" {:attribute attribute :row row :value value}))
                     (let [destination (+ base component)
                           before (aget target-values destination)
                           level (case blend :replace value :add (+ before value) :max (max before value))]
                       (when-not (and (Double/isFinite level) (<= 0.0 level) (<= level 1.0))
                         (fail! "Blended assignment exceeds its finite attribute range"
                                {:target-id (nth target-ids row) :attribute attribute :value level}))
                       (aset-double target-values destination level)
                       (aset-boolean target-present destination true))))))))
         (pack-dense-state patch target-values target-present options))
       (let [assignments (vec (for [{:keys [target-ids columns blend]} batches
                                   row (range (count target-ids))
                                   {:keys [attribute components values]} columns]
                               {:target-id (nth target-ids row) :attribute attribute :blend blend
                                :value (if (= 1 components) (aget ^doubles values row)
                                           (mapv #(aget ^doubles values (+ (* row components) %)) (range components)))}))]
         (resolve-frame patch assignments options))))))

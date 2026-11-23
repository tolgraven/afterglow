(ns afterglow.control.devices.expressive
  "Pure, portable expressive mappings shared by MPE devices and Studio."
  (:require [clojure.string :as str]
            [afterglow.control.bindings :as bindings]
            [afterglow.control.codecs.mpe :as mpe]
            [afterglow.control.params :as params]))

(def curves #{:linear :ease-in :ease-out :smoothstep})
(def semantic-axes
  {:level :pressure :dimmer :pressure :brightness :pressure :intensity :pressure
   :velocity :strike :strike :strike :pressure :pressure :aftertouch :pressure
   :pan :glide :azimuth :glide :rotation :glide :tilt :slide :elevation :slide
   :focus :slide :zoom :slide :slide :slide :glide :glide :lift :lift})
(def max-mapped-parameters 62)

(defn- fail! [path message]
  (throw (ex-info message {:expressive/error :invalid-policy :errors [{:path path :message message}]})))
(defn- identifier? [x] (or (keyword? x) (and (string? x) (<= 1 (count x) 128))))
(defn- kw [x] (if (string? x) (keyword x) x))
(defn- finite-pair? [x]
  (and (vector? x) (= 2 (count x)) (every? params/finite-number? x)))
(defn- normalize-binding [value path]
  (cond
    (nil? value) nil
    (or (keyword? value) (string? value)) (normalize-binding {:axis value} path)
    (vector? value)
    (do (when-not (<= 1 (count value) 16) (fail! path "Use one to sixteen component mappings"))
        (when (some vector? value) (fail! path "Component mappings cannot be nested"))
        (mapv #(normalize-binding %1 (conj path %2)) value (range)))
    (map? value)
    (let [binding (cond-> value (contains? value :axis) (update :axis kw)
                                (contains? value :curve) (update :curve kw))]
      (when-not (every? #{:axis :component :range :input-range :curve :inverted? :enabled?} (keys binding))
        (fail! path "Unknown mapping option"))
      (doseq [flag [:enabled? :inverted?] :when (contains? binding flag)]
        (when-not (boolean? (get binding flag)) (fail! (conj path flag) "Mapping flag must be boolean")))
      (when-not (or (false? (:enabled? binding)) (contains? mpe/axes (:axis binding)))
        (fail! (conj path :axis) "Choose a documented expressive axis"))
      (when (and (contains? binding :component)
                 (not (and (integer? (:component binding)) (<= 0 (:component binding) 15))))
        (fail! (conj path :component) "Component must be an integer from zero to fifteen"))
      (doseq [field [:range :input-range] :when (contains? binding field)]
        (when-not (finite-pair? (get binding field)) (fail! (conj path field) "Range needs two finite endpoints")))
      (when-let [[low high] (:input-range binding)]
        (when-not (< low high) (fail! (conj path :input-range) "Input range must increase")))
      (when-not (curves (:curve binding :linear)) (fail! (conj path :curve) "Unknown response curve"))
      binding)
    :else (fail! path "Mapping must be an axis, a mapping map, component mappings, or nil to disable")))

(defn normalize-policy
  "Validate a portable device/cue mapping policy. JSON axis names normalize to
  keywords; identifiers retain their spelling. Device policies may contain :cues."
  ([policy] (normalize-policy policy [] true))
  ([policy path device?]
   (when-not (and (map? policy)
                  (every? (if device? #{:enabled? :auto? :disabled-axes :params :cues}
                                      #{:enabled? :auto? :disabled-axes :params}) (keys policy)))
     (fail! path "Unknown or malformed expressive mapping policy"))
   (doseq [flag [:enabled? :auto?] :when (contains? policy flag)]
     (when-not (boolean? (get policy flag)) (fail! (conj path flag) "Policy flag must be boolean")))
   (when (contains? policy :disabled-axes)
     (when-not (and (or (set? (:disabled-axes policy)) (vector? (:disabled-axes policy)))
                    (every? #(contains? mpe/axes (kw %)) (:disabled-axes policy)))
       (fail! (conj path :disabled-axes) "Disabled axes must name documented expressive axes")))
   (when (contains? policy :params)
     (when-not (and (map? (:params policy)) (<= (count (:params policy)) max-mapped-parameters)
                    (every? keyword? (keys (:params policy))))
       (fail! (conj path :params) "Parameter mappings need keyword IDs and at most 62 entries")))
   (when (contains? policy :cues)
     (when-not (and device? (map? (:cues policy)) (<= (count (:cues policy)) 4096)
                    (every? identifier? (keys (:cues policy))))
       (fail! (conj path :cues) "Cue policies must be a map of cue IDs")))
   (cond-> policy
     (contains? policy :disabled-axes) (update :disabled-axes #(set (map kw %)))
     (contains? policy :params) (update :params #(into {} (map (fn [[id value]]
                                                              [id (normalize-binding value (conj path :params id))])) %))
     (contains? policy :cues) (update :cues #(into {} (map (fn [[id value]]
                                                          [id (normalize-policy value (conj path :cues id) false)])) %)))))

(defn normalize-config
  "Validate [:settings :expressive]. Restoring this data never opens a device."
  [config]
  (when-not (and (map? config) (every? #{:devices} (keys config))
                 (map? (:devices config {})) (<= (count (:devices config {})) 64)
                 (every? identifier? (keys (:devices config {}))))
    (fail! [] "Expressive settings need a map of up to 64 device profiles"))
  (update config :devices #(into {} (map (fn [[id policy]]
                                         [id (normalize-policy policy [:devices id] true)])) %)))

(defn- lookup [entries id]
  (or (get entries id)
      (when (identifier? id)
        (get entries (if (keyword? id) (subs (str id) 1) (keyword id))))))

(defn profile-defaults
  "Shared profile-option defaults for a cue, before persisted show policy."
  [options cue-id]
  (let [base (:mapping-policy options {}) cue (lookup (:cues base) cue-id)]
    (-> (merge base cue)
        (dissoc :cues)
        (assoc :enabled? (not-any? #(false? (:enabled? %)) [base cue])
               :disabled-axes (set (concat (:disabled-axes base) (:disabled-axes cue)))
               :params (merge {} (:params base) (:param-mappings options) (:params cue)
                              (lookup (:cue-mappings options) cue-id))))))

(defn policy
  "Resolve captured profile defaults, device settings and cue overrides. Device
  disable is a master expression switch; it never prevents note-off cleanup."
  [model device-id cue-id defaults]
  (let [device (lookup (get-in model [:settings :expressive :devices]) device-id)
        cue (lookup (:cues device) cue-id)
        merged (merge {:enabled? true :auto? true} defaults device cue)]
    (-> merged
        (dissoc :cues)
        (assoc :enabled? (not-any? #(false? (:enabled? %)) [defaults device cue])
               :params (merge {} (:params defaults) (:params device) (:params cue))
               :disabled-axes (set (mapcat :disabled-axes [defaults device cue]))))))

(defn- semantic-axis [parameter schema]
  (or (get semantic-axes (kw (:control/semantic schema)))
      (get semantic-axes (keyword (name parameter)))
      (some semantic-axes (map keyword (str/split (str/lower-case (str (:name schema ""))) #"[^a-z]+")))))

(defn- scalar-bounds [schema]
  (if (= :color (:type schema)) (params/color-bounds schema) (:bounds schema)))

(defn- supported? [{:keys [type size] :as schema} {:keys [component range]}]
  (and (params/valid-schema? schema)
       (if (#{:color :vector :range} type)
         (and (integer? component) (< component (case type :color 3 :range 2 size)))
         (nil? component))
       (or (#{:boolean :enum} type) (finite-pair? (or range (scalar-bounds schema))))))

(defn- valid-range? [schema {:keys [range input-range axis]}]
  (let [bounds (scalar-bounds schema) output (or range bounds) input (get-in mpe/axes [axis :range])]
    (and (or (nil? range)
             (and (not (#{:enum :boolean} (:type schema)))
                  (or (nil? bounds) (every? #(<= (first bounds) % (second bounds)) range))))
         (or (not= :integer (:type schema))
             (<= (Math/ceil (double (apply min output))) (Math/floor (double (apply max output)))))
         (or (nil? input-range)
             (every? #(<= (first input) % (second input)) input-range)))))

(defn plan
  "Produce a reviewable plan. Manual bindings override annotations and semantic
  auto mapping; nil disables a parameter. :auto? false retains explicit bindings.
  Compound parameters need component mappings. Invalid targets yield diagnostics."
  ([schemas available] (plan schemas available {} {}))
  ([schemas available overrides] (plan schemas available overrides {}))
  ([schemas available overrides options]
   (let [options (assoc (normalize-policy (dissoc options :params)) :params
                        (into {} (map (fn [[id binding]] [id (normalize-binding binding [:params id])])) overrides))
         available (set available)
         entries
         (mapcat
          (fn [parameter]
            (let [schema (get schemas parameter)
                  explicit? (or (contains? overrides parameter) (contains? schema :control/axis))
                  inferred (when (get options :auto? true) (semantic-axis parameter schema))
                  raw (cond (contains? overrides parameter) (get-in options [:params parameter])
                            (contains? schema :control/axis) (:control/axis schema)
                            :else inferred)
                  bindings (if (vector? raw) raw [raw])]
              (for [raw bindings
                    :let [binding (if (keyword? raw) {:axis raw} raw) axis (:axis binding)]]
                (cond
                  (nil? schema) {:diagnostic {:param parameter :code :unknown-parameter}}
                  (false? (:enabled? options)) {:disabled parameter :reason {:param parameter :code :policy-disabled}}
                  (or (and explicit? (nil? raw)) (false? (:enabled? binding)))
                  {:disabled parameter :reason {:param parameter :code :parameter-disabled}}
                  (nil? raw) nil
                  (contains? (:disabled-axes options) axis)
                  {:disabled parameter :reason {:param parameter :axis axis :code :axis-disabled}}
                  (not (contains? available axis)) {:diagnostic {:param parameter :axis axis :code :unavailable-axis}}
                  (not (supported? schema binding)) {:diagnostic {:param parameter :axis axis :code :unsupported-schema}}
                  (not (valid-range? schema binding)) {:diagnostic {:param parameter :axis axis :code :invalid-range}}
                  :else {:mapping (assoc binding :param parameter :schema schema :origin (if explicit? :explicit :automatic))}))))
          (sort-by str (set (concat (keys schemas) (keys overrides)))))
         mappings (vec (keep :mapping entries))
         admitted (set (take max-mapped-parameters (distinct (map :param mappings))))]
     {:mappings (filterv #(admitted (:param %)) mappings)
      :diagnostics (cond-> (vec (keep :diagnostic entries))
                     (> (count (distinct (map :param mappings))) max-mapped-parameters)
                     (conj {:code :mapping-limit :limit max-mapped-parameters}))
      :suggestions [] :disabled (vec (distinct (keep :disabled entries)))
      :disabled-reasons (vec (distinct (keep :reason entries)))})))

(defn mapped-value
  "Map an axis through a bounded range/curve, preserving other components."
  ([mapping value] (mapped-value mapping value (get-in mapping [:schema :default])))
  ([{:keys [axis schema input-range range curve inverted? component]} value current]
   (let [unit (bindings/scale value (or input-range (get-in mpe/axes [axis :range])) [0.0 1.0])
         unit (if inverted? (- 1 unit) unit)
         unit (case curve :ease-in (* unit unit) :ease-out (- 1 (* (- 1 unit) (- 1 unit)))
                          :smoothstep (* unit unit (- 3 (* 2 unit))) unit)
         {:keys [type values options]} schema
         output (or range (scalar-bounds schema))
         scalar (case type
                  :boolean (>= unit 0.5)
                  :enum (let [choices (or values options)] (nth choices (min (dec (count choices)) (int (* unit (count choices))))))
                  :integer (long (bindings/clamp (Math/round (double (bindings/scale unit [0 1] output)))
                                                  [(Math/ceil (double (apply min output))) (Math/floor (double (apply max output)))]))
                  (bindings/scale unit [0 1] output))]
     (if (some? component)
       (let [current (if (params/valid-value? schema current) current (:default schema))
             scalar (if (= type :range)
                      (if (zero? component) (min scalar (second current)) (max scalar (first current))) scalar)]
         (assoc current component scalar))
       scalar))))

(defn values
  "Return only parameters touched by this event, preserving their other components."
  ([mapping-plan axis-values] (values mapping-plan axis-values {}))
  ([mapping-plan axis-values current]
   (reduce (fn [result {:keys [param axis schema] :as mapping}]
             (if (contains? axis-values axis)
               (assoc result param (mapped-value mapping (get axis-values axis)
                                                 (get result param (get current param (:default schema))))) result))
           {} (:mappings mapping-plan))))

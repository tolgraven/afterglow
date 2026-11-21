(ns afterglow.control.devices.expressive
  "Pure schema-driven expressive mapping shared by MPE devices and other inputs."
  (:require [afterglow.control.bindings :as bindings]
            [afterglow.control.codecs.mpe :as mpe]
            [afterglow.control.params :as params]))

(def ^:private suggestions
  {:level :pressure :dimmer :pressure :velocity :strike :pan :glide :tilt :slide
   :focus :slide :zoom :slide})

(defn- supported-schema? [{:keys [type bounds] :as schema}]
  (and (params/valid-schema? schema)
       (or (#{:boolean :enum} type)
           (and (#{:number :integer} type) bounds
                (or (= type :number)
                    (<= (Math/ceil (double (first bounds))) (Math/floor (double (second bounds)))))))))

(defn plan
  "Build automatic mappings only from schema :control/axis annotations and the
  available device axes. Explicit {parameter axis-or-nil} overrides annotations.
  Unannotated familiar names produce suggestions, never silent assignments."
  ([schemas available] (plan schemas available {}))
  ([schemas available overrides]
   (let [available (set available)
         entries (for [parameter (sort-by str (set (concat (keys schemas) (keys overrides))))
                       :let [schema (get schemas parameter)
                             annotated? (or (contains? overrides parameter) (contains? schema :control/axis))
                             axis (if (contains? overrides parameter) (get overrides parameter) (:control/axis schema))]]
                   (cond
                     (nil? schema) {:diagnostic {:param parameter :code :unknown-parameter}}
                     (and annotated? (nil? axis)) {:disabled parameter}
                     (and annotated? (not (contains? mpe/axes axis))) {:diagnostic {:param parameter :axis axis :code :unknown-axis}}
                     (and annotated? (not (contains? available axis))) {:diagnostic {:param parameter :axis axis :code :unavailable-axis}}
                     (and annotated? (not (supported-schema? schema))) {:diagnostic {:param parameter :axis axis :code :unsupported-schema}}
                     annotated? {:mapping {:param parameter :axis axis :schema schema}}
                     (and (contains? available (get suggestions parameter)) (supported-schema? schema))
                     {:suggestion {:param parameter :axis (get suggestions parameter) :reason :conventional-parameter-name
                                   :requires-confirmation? true}}
                     :else nil))]
     {:mappings (vec (keep :mapping entries)) :diagnostics (vec (keep :diagnostic entries))
      :suggestions (vec (keep :suggestion entries)) :disabled (vec (keep :disabled entries))})))

(defn mapped-value
  "Map a normalized axis to bounded number/integer, boolean or enum. Integer
  outputs stay inside integer bounds. Glide center maps to the range midpoint."
  [{:keys [axis schema]} value]
  (let [unit (bindings/scale value (get-in mpe/axes [axis :range]) [0.0 1.0])
        {:keys [type bounds values options]} schema]
    (case type
      :number (bindings/scale unit [0 1] bounds)
      :integer (let [low (long (Math/ceil (double (first bounds))))
                     high (long (Math/floor (double (second bounds))))]
                 (long (bindings/clamp (Math/round (double (bindings/scale unit [0 1] [low high]))) [low high])))
      :boolean (>= unit 0.5)
      :enum (let [choices (or values options)] (nth choices (min (dec (count choices)) (int (* unit (count choices)))))))))

(defn values
  "Return only mapped parameters whose axes occur in this event."
  [mapping-plan axis-values]
  (into {} (keep (fn [{:keys [param axis] :as mapping}]
                   (when (contains? axis-values axis) [param (mapped-value mapping (get axis-values axis))])))
        (:mappings mapping-plan)))

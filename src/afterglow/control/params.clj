(ns afterglow.control.params
  "Pure parameter validation shared by control adapters. No coercion or I/O.")

(defn finite-number? [value]
  (and (number? value) (Double/isFinite (double value))))

(defn color-bounds [schema]
  (let [[low high] (or (:bounds schema) [0 1])]
    [(max 0 low) (min 1 high)]))

(defn- linear-rgb? [bounded? value]
  (and (vector? value) (= 3 (count value))
       (every? #(and (bounded? %) (<= 0 % 1)) value)))

(defn valid-value?
  "Does value satisfy a parameter schema? Bounds are inclusive; unknown types
  are rejected. Color is three linear RGB components in [0,1]. Gradients are
  nonempty vectors of {:position t :color rgb} stops in strictly increasing
  position order within [0,1]. A single stop represents a solid color."
  [{:keys [type bounds values options size]} value]
  (let [bounded? (fn [v]
                   (and (finite-number? v)
                        (or (nil? bounds)
                            (and (vector? bounds) (= 2 (count bounds))
                                 (every? finite-number? bounds)
                                 (<= (first bounds) v (second bounds))))))]
    (case type
      :number (bounded? value)
      :integer (and (integer? value) (bounded? value))
      :boolean (instance? Boolean value)
      :enum (and (vector? (or values options))
                 (boolean (some #(= value %) (or values options))))
      :color (linear-rgb? bounded? value)
      :gradient (and (vector? value) (seq value)
                     (every? (fn [stop]
                               (and (map? stop) (= #{:position :color} (set (keys stop)))
                                    (let [{:keys [position color]} stop]
                                      (and (finite-number? position) (<= 0 position 1)
                                           (linear-rgb? bounded? color)))))
                             value)
                     (apply < (map :position value)))
      :vector (and (vector? value) (or (nil? size) (= size (count value)))
                   (every? bounded? value))
      :range (and (vector? value) (= 2 (count value))
                  (every? bounded? value) (<= (first value) (second value)))
      false)))

(defn valid-schema?
  "Check the core schema contract before publishing a definition."
  [{:keys [type bounds values options size] :as schema}]
  (and (map? schema)
       (#{:number :integer :boolean :enum :color :gradient :vector :range} type)
       (or (nil? bounds)
           (and (vector? bounds) (= 2 (count bounds))
                (every? finite-number? bounds) (<= (first bounds) (second bounds))))
       (or (not= type :enum) (and (vector? (or values options)) (seq (or values options))))
       (or (not= type :vector) (and (integer? size) (pos? size)))
       (contains? schema :default)
       (valid-value? schema (:default schema))))

(defn validate-values
  "Return path/message errors for overrides; absent values are allowed here."
  [schemas values]
  (if-not (map? values)
    [{:path [] :message "Parameters must be a map"}]
    (into []
          (keep (fn [[k value]]
                  (cond
                    (not (contains? schemas k))
                    {:path [k] :message "Unknown parameter"}
                    (not (valid-value? (get schemas k) value))
                    {:path [k] :message "Value does not satisfy parameter schema"})))
          values)))

(defn dependent-cue-errors
  "Report overrides that would become invalid if this effect revision were
  published. Archived and pinned cues keep their captured effect schema."
  [cues effect]
  (into [] (for [[id cue] cues
                 :when (and (= (:id effect) (:effect-id cue)) (not (:effect-version cue)))
                 field [:params :saved-params]
                 :when (contains? cue field)
                 error (validate-values (:params effect {}) (get cue field))]
             (update error :path #(into [:cues id field] %)))))

(defn resolve-values
  "Merge schema defaults and overrides; throw with validation errors if invalid."
  [schemas overrides]
  (let [values (merge (into {} (map (fn [[k spec]] [k (:default spec)])) schemas)
                      overrides)
        errors (validate-values schemas values)]
    (when (seq errors)
      (throw (ex-info "Invalid parameters" {:errors errors})))
    values))

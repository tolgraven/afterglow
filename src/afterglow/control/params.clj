(ns afterglow.control.params
  "Pure parameter validation shared by control adapters. No coercion or I/O.")

(defn finite-number? [value]
  (and (number? value) (Double/isFinite (double value))))

(defn valid-value?
  "Does value satisfy a parameter schema? Bounds are inclusive; unknown types
  are rejected. Color is three linear RGB components in [0,1]."
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
      :color (and (vector? value) (= 3 (count value))
                  (every? #(and (finite-number? %) (<= 0 % 1)) value))
      :vector (and (vector? value) (or (nil? size) (= size (count value)))
                   (every? bounded? value))
      :range (and (vector? value) (= 2 (count value))
                  (every? bounded? value) (<= (first value) (second value)))
      false)))

(defn valid-schema?
  "Check the core schema contract before publishing a definition."
  [{:keys [type bounds values options size] :as schema}]
  (and (map? schema)
       (#{:number :integer :boolean :enum :color :vector :range} type)
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

(defn resolve-values
  "Merge schema defaults and overrides; throw with validation errors if invalid."
  [schemas overrides]
  (let [values (merge (into {} (map (fn [[k spec]] [k (:default spec)])) schemas)
                      overrides)
        errors (validate-values schemas values)]
    (when (seq errors)
      (throw (ex-info "Invalid parameters" {:errors errors})))
    values))

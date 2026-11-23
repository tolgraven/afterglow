(ns afterglow.control.parameter-edit
  "Pure typed editing for encoders, touch strips and other normalized controls.
  No device addresses, mutable state, clocks or command admission live here."
  (:require [afterglow.control.bindings :as bindings]
            [afterglow.control.params :as params]))

(defn ordered-parameters
  "Explicit :param-order wins; schema :order and stable key order fill the rest."
  [definition]
  (let [schemas (:params definition)
        explicit (distinct (filter #(contains? schemas %) (:param-order definition)))
        remaining (remove (set explicit) (keys schemas))]
    (vec (concat explicit (sort-by (fn [id] [(let [order (get-in schemas [id :order])]
                                             (if (params/finite-number? order) order Double/POSITIVE_INFINITY))
                                           (str id)]) remaining)))))

(defn components [schema]
  (case (:type schema)
    :color [:hue :saturation :brightness]
    :range [:lower :upper]
    :vector (mapv #(keyword (str "component-" (inc %))) (range (:size schema)))
    [:value]))

(defn rgb->hsv [[r g b]]
  (let [hi (max r g b) lo (min r g b) delta (- hi lo)
        h (cond (zero? delta) 0.0
                (= hi r) (mod (/ (- g b) delta) 6.0)
                (= hi g) (+ 2.0 (/ (- b r) delta))
                :else (+ 4.0 (/ (- r g) delta)))]
    [(/ h 6.0) (if (zero? hi) 0.0 (/ delta hi)) hi]))

(defn hsv->rgb [[h s v]]
  (let [h (* (mod h 1.0) 6.0) chroma (* v s)
        x (* chroma (- 1.0 (Math/abs (- (mod h 2.0) 1.0))))
        base (- v chroma)
        rgb (case (int (Math/floor h))
              0 [chroma x 0] 1 [x chroma 0] 2 [0 chroma x]
              3 [0 x chroma] 4 [x 0 chroma] [chroma 0 x])]
    (mapv #(double (bindings/clamp (+ base %) [0 1])) rgb)))

(defn- color-to-control [schema rgb]
  (let [[low high] (params/color-bounds schema)]
    (mapv #(if (== low high) 0.0 (/ (- % low) (- high low))) rgb)))

(defn- control-to-color [schema rgb]
  (let [[low high] (params/color-bounds schema)]
    (mapv #(bindings/clamp (+ low (* % (- high low))) [low high]) rgb)))

(defn- numeric-range [schema value]
  (or (:bounds schema) [(- (double value) 1.0) (+ (double value) 1.0)]))

(defn- step [schema bounds fine?]
  (let [declared (:step schema)
        base (cond (= :integer (:type schema)) (if (and (integer? declared) (pos? declared)) declared 1)
                   (and (params/finite-number? declared) (pos? declared)) declared
                   :else (/ (- (second bounds) (first bounds)) 100.0))]
    (if (and fine? (not= :integer (:type schema))) (/ base 10.0) base)))

(defn- discrete-index [values value]
  (or (first (keep-indexed #(when (= %2 value) %1) values)) 0))

(defn- component-index [schema component]
  (min (dec (count (components schema))) (max 0 (long (or component 0)))))

(defn edit
  "Return a schema-valid value for relative delta or absolute normalized input.
  Options: :mode :relative|:absolute, :component index and :fine?. Enum values
  (including waveform selections) are returned unchanged. Range endpoints never
  cross. Color components are HSV editing over the model's linear RGB values."
  [schema value input {:keys [mode component fine?] :or {mode :relative} :as options}]
  (when-not (and (params/valid-value? schema value) (params/finite-number? input)
                 (#{:relative :absolute} mode))
    (throw (ex-info "Typed editing needs a valid value, finite input and supported mode" {})))
  (let [component (component-index schema component)
        absolute? (= :absolute mode)
        fraction (when absolute? (bindings/clamp input [0 1]))
        number-edit (fn [current bounds]
                      (let [result (if absolute?
                                     (+ (first bounds) (* fraction (- (second bounds) (first bounds))))
                                     (+ current (* input (step schema (or (:bounds schema) bounds) fine?))))]
                        (bindings/clamp result bounds)))
        result
        (case (:type schema)
          (:number :integer)
          (let [bounds (numeric-range schema value) result (number-edit value bounds)]
            (if (= :integer (:type schema))
              (long (bindings/clamp (Math/round (double result))
                                    [(Math/ceil (double (first bounds))) (Math/floor (double (second bounds)))])) result))
          :boolean (if absolute? (>= fraction 0.5) (cond (pos? input) true (neg? input) false :else value))
          :enum (let [values (or (:values schema) (:options schema))
                      index (if absolute? (min (dec (count values)) (long (* fraction (count values))))
                                (+ (discrete-index values value) (long input)))]
                  (nth values (int (bindings/clamp index [0 (dec (count values))]))))
          :color (let [hsv (rgb->hsv (color-to-control schema value))
                       changed (if (and (zero? component) (not absolute?))
                                 (mod (+ (nth hsv component) (* input (if fine? 0.001 0.01))) 1.0)
                                 (if absolute? fraction
                                     (bindings/clamp (+ (nth hsv component) (* input (if fine? 0.001 0.01))) [0 1])))]
                   (control-to-color schema (hsv->rgb (assoc hsv component changed))))
          (:vector :range)
          (let [bounds (numeric-range schema (nth value component))
                bounds (if (= :range (:type schema))
                         (if (zero? component) [(first bounds) (second value)] [(first value) (second bounds)]) bounds)]
            (assoc value component (number-edit (nth value component) bounds))))]
    (when-not (params/valid-value? schema result)
      (throw (ex-info "Typed edit did not satisfy its parameter schema" {:type (:type schema)})))
    result))

(defn color-grid-value
  "Eight grayscale choices on the first row, then hue/saturation choices."
  ([x y] (color-grid-value {} x y))
  ([schema x y]
   (control-to-color schema (if (zero? y) (vec (repeat 3 (/ x 7.0)))
                               (hsv->rgb [(/ x 8.0) (/ y 7.0) 1.0])))))

(defn position
  "Project the selected typed component to the same normalized range used by
  absolute editing. Used for control feedback, with no MIDI/device dependency."
  [schema value {:keys [component]}]
  (when-not (params/valid-value? schema value)
    (throw (ex-info "Control feedback needs a valid parameter value" {})))
  (let [component (component-index schema component)
        normalized (fn [value [low high]]
                     (if (= low high) 0.0 (bindings/clamp (/ (- value low) (- high low)) [0 1])))]
    (case (:type schema)
      (:number :integer) (normalized value (numeric-range schema value))
      :boolean (if value 1.0 0.0)
      :enum (let [values (or (:values schema) (:options schema))]
              (if (= 1 (count values)) 0.0 (/ (discrete-index values value) (double (dec (count values))))))
      :color (nth (rgb->hsv (color-to-control schema value)) component)
      :vector (normalized (nth value component) (numeric-range schema (nth value component)))
      :range (let [[low high] (numeric-range schema (nth value component))]
               (normalized (nth value component)
                           (if (zero? component) [low (second value)] [(first value) high]))))))

(defn velocity-values
  "Map a normalized velocity/pressure into explicitly enabled numeric params.
  Per-parameter velocity endpoints may reverse direction, but final values
  remain inside the declared schema bounds. Integer parameters stay integers."
  [definition input]
  (when-not (params/finite-number? input)
    (throw (ex-info "Velocity must be finite" {})))
  (let [fraction (bindings/clamp input [0 1])]
    (into {}
          (for [[id schema] (:params definition)
                :when (and (:velocity schema) (#{:number :integer} (:type schema)))
                :let [[low high] (or (:bounds schema) [0 1])
                      from (:velocity-min schema low) to (:velocity-max schema high)
                      _ (when-not (every? params/finite-number? [from to])
                          (throw (ex-info "Velocity endpoints must be finite" {:param id})))
                      value (+ from (* fraction (- to from)))
                      value (if (:bounds schema) (bindings/clamp value (:bounds schema)) value)
                      value (if (= :integer (:type schema))
                              (let [rounded (Math/round (double value))]
                                (if (:bounds schema)
                                  (long (bindings/clamp rounded
                                          [(Math/ceil (double low)) (Math/floor (double high))])) rounded)) value)
                      _ (when-not (params/valid-value? schema value)
                          (throw (ex-info "Velocity result must satisfy parameter schema" {:param id})))]]
            [id value]))))

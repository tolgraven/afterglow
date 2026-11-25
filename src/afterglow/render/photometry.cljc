(ns afterglow.render.photometry
  "Portable fixture optics and full-white brightness for the renderer and Studio.")

(def fixture-keys
  [:beam-angle :zoom-range-deg :lens-radius-m :pseudo-fixture :max-watts :measured-relative-brightness])

(defn- positive-finite? [x]
  (and (number? x) (#?(:clj Double/isFinite :cljs js/Number.isFinite) (double x)) (pos? x)))

(defn- angle? [x] (and (positive-finite? x) (< x 180)))

(def ^:private specs
  [[:beam-angle angle? "Full beam angle must be greater than 0 and less than 180 degrees"]
   [:zoom-range-deg #(and (vector? %) (= 2 (count %)) (every? angle? %))
    "Zoom needs two full beam angles in DMX order, each between 0 and 180 degrees"]
   [:lens-radius-m #(or (positive-finite? %) (and (number? %) (zero? %)))
    "Lens radius must be nonnegative finite metres"]
   [:max-watts positive-finite? "Maximum electrical power must be positive finite watts"]
   [:measured-relative-brightness positive-finite? "Measured full-white brightness must be a positive finite ratio"]
   [:pseudo-fixture boolean? "Pseudo-fixture must be true or false"]
   [:emission-share #(and (number? %) (<= 0 % 1)) "The head's share of total output must be between 0 and 1"]])

(defn errors
  "Validate optional optical properties without filling defaults."
  [fixture]
  (vec
   (for [[key valid? message] specs
         :when (and (contains? fixture key) (not (valid? (get fixture key))))]
     {:path [key] :message message})))

(def emitter-spectrum
  "Additive emitter channels mapped to [relative photopic response, linear RGB
  preview tint]. Responses approximate CIE Vλ at representative wavelengths,
  including cyan at 505 nm and lime at 560 nm. Broadband white uses 300 lm per
  optical watt. UV emits physical output with no visible contribution."
  (let [white (/ 300.0 683.0)
        cold [white [0.82 0.9 1.0]]]
    {:red [0.321 [1.0 0.0 0.0]] :green [0.793 [0.0 1.0 0.0]] :blue [0.074 [0.0 0.0 1.0]]
     :white [white [1.0 1.0 1.0]] :amber [0.757 [1.0 0.55 0.0]]
     :warm-white [white [1.0 0.8 0.62]] :cold-white cold :cool-white cold
     :cyan [0.407 [0.0 1.0 0.8]] :lime [0.995 [0.55 1.0 0.06]] :uv [0.0 [0.0 0.0 0.0]]}))

(def ^:private white-response (into {} (map (fn [[k [response]]] [k response])) emitter-spectrum))

(def ^:private rgb-white (/ (+ (:red white-response) (:green white-response) (:blue white-response)) 3))

(defn relative-brightness
  "Estimate the full-white visible output of one fixture relative to a 100 W
  RGB fixture. The wattage model assumes equal electrical shares per emitter
  and equal conversion efficiencies. A calibrated ratio wins. With neither
  measurement nor power, share unit fixture output among its heads."
  [{:keys [max-watts measured-relative-brightness channels emission-share] :or {emission-share 1.0}}]
  (cond
    (some? measured-relative-brightness) (* emission-share (double measured-relative-brightness))
    (nil? max-watts) (double emission-share)
    :else
    (let [weights (keep white-response (keys channels))
          response (if (seq weights) (/ (reduce + weights) (count weights)) (:white white-response))]
      (* emission-share (/ (double max-watts) 100) (/ response rgb-white)))))

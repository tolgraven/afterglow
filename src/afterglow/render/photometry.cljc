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
   [:lens-radius-m positive-finite? "Lens radius must be positive finite metres"]
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

;; Relative photopic sensitivity at representative emitter wavelengths (CIE Vλ).
;; Broadband white assumes 300 lm per optical watt; UV contributes no visible light.
(def ^:private white-response
  {:red 0.321 :green 0.793 :blue 0.074 :amber 0.757 :white (/ 300.0 683.0) :warm-white (/ 300.0 683.0) :cold-white (/ 300.0 683.0) :uv 0.0})

(def ^:private rgb-white (/ (+ (:red white-response) (:green white-response) (:blue white-response)) 3))

(defn relative-brightness
  "Estimate the full-white visible output of one fixture relative to a 100 W
  RGB fixture. The wattage model assumes equal electrical shares per emitter
  and equal conversion efficiencies. A calibrated ratio wins. With neither
  measurement nor power, preserve the preview's unit gain."
  [{:keys [max-watts measured-relative-brightness channels emission-share] :or {emission-share 1.0}}]
  (cond
    (some? measured-relative-brightness) (* emission-share (double measured-relative-brightness))
    (nil? max-watts) 1.0
    :else
    (let [weights (keep white-response (keys channels))
          response (if (seq weights) (/ (reduce + weights) (count weights)) (:white white-response))]
      (* emission-share (/ (double max-watts) 100) (/ response rgb-white)))))

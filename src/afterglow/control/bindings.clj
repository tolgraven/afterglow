(ns afterglow.control.bindings
  "Composable, pure input transformations and held-gesture lifecycle. Adapters
  own physical events, clocks and sends; these helpers only return data."
  (:require [afterglow.control.params :as params]))

(defn clamp [value [low high]]
  (when-not (and (every? params/finite-number? [value low high]) (<= low high))
    (throw (ex-info "Clamp needs finite value and ordered bounds" {})))
  (max low (min high value)))

(defn scale
  "Linearly map a value; input is clamped by default. Reversed output ranges
  support inverted controls, but input bounds must increase."
  ([value input output] (scale value input output true))
  ([value [low high :as input] [out-low out-high] clamp?]
   (when-not (and (every? params/finite-number? [value low high out-low out-high]) (< low high))
     (throw (ex-info "Scale needs finite values and increasing input bounds" {})))
   (+ out-low (* (/ (- (if clamp? (clamp value input) value) low) (- high low))
                 (- out-high out-low)))))

(defn quantize [value step origin]
  (when-not (and (every? params/finite-number? [value step origin]) (pos? step))
    (throw (ex-info "Quantization step must be finite and positive" {})))
  (+ origin (* step (Math/round (double (/ (- value origin) step))))))

(defn input-matches? [event pattern]
  (every? (fn [[k v]] (= v (get event k))) pattern))

(defn reset-pickup
  "Reset soft takeover after an external parameter change."
  [state target]
  (assoc state :target target :picked-up? false :last-input nil))

(defn apply-input
  "Map a normalized input event through one binding.

  Binding: :event partial match, :command command template, :mode :absolute or
  :relative, :input-range (default [0,1]), :output-range, optional :step,
  :value-key (default :value), :pickup? and :target-value. Relative mode uses
  :step as sensitivity and accumulates from state's :value or target-value.
  Return {:state next-state :commands [...]}; no command is sent here."
  [state event binding envelope]
  (if-not (input-matches? event (:event binding))
    {:state state :commands []}
    (let [mode (get binding :mode :absolute)
          _ (when-not (#{:absolute :relative} mode)
              (throw (ex-info "Unknown binding mode" {:mode mode})))
          [low high :as output] (get binding :output-range [0.0 1.0])
          _ (clamp low output)
          raw (get event (get binding :value-key :value))
          target (get state :target (get binding :target-value low))
          value (if (= mode :relative)
                  (let [step (get binding :step 1)]
                    (when-not (and (params/finite-number? raw) (params/finite-number? step) (pos? step))
                      (throw (ex-info "Relative input and sensitivity must be finite" {})))
                    (clamp (+ (get state :value target) (* step raw)) output))
                  (let [mapped (scale raw (get binding :input-range [0.0 1.0]) output)]
                    (if-let [step (:step binding)]
                      (clamp (quantize mapped step low) output) mapped)))
          previous (:last-input state)
          tolerance (get binding :pickup-tolerance 0.01)
          _ (when-not (and (params/finite-number? tolerance) (<= 0 tolerance))
              (throw (ex-info "Pickup tolerance must be nonnegative" {})))
          picked? (or (= mode :relative) (not (:pickup? binding)) (:picked-up? state)
                      (<= (Math/abs (double (- value target))) tolerance)
                      (and (some? previous) (<= (min previous value) target (max previous value))))
          next-state (cond-> (assoc state :last-input value :picked-up? (boolean picked?))
                       picked? (assoc :value value))]
      {:state next-state
       :commands (if picked?
                   [(merge (:command binding) envelope {:value value})] [])})))

(defn begin-hold
  "Launch a held cue. Retain the returned gesture ID until its corresponding
  physical release; never look up an instance by cue identity."
  [state cue-id envelope]
  (let [id (or (:gesture-id envelope) (:command-id envelope))]
    (when (contains? (:gestures state) id)
      (throw (ex-info "Gesture already exists" {:gesture-id id})))
    {:state (assoc-in state [:gestures id] {:pressed? true})
     :gesture-id id
     :commands [(merge envelope {:op :cue/launch :cue-id cue-id :gesture-id id
                                 :launch {:mode :held}})]}))

(defn end-hold
  "Release a gesture, retaining early release data until launch acknowledgement
  arrives. Unknown/already released gestures do not emit another command."
  [state gesture-id envelope]
  (if-let [gesture (get-in state [:gestures gesture-id])]
    (cond
      (not (:pressed? gesture)) {:state state :commands []}
      (:instance-id gesture)
      {:state (update state :gestures dissoc gesture-id)
       :commands [(merge envelope {:op :instance/end :instance-id (:instance-id gesture)})]}
      :else {:state (assoc-in state [:gestures gesture-id]
                             (assoc gesture :pressed? false :release-envelope envelope))
             :commands []})
    {:state state :commands []}))

(defn acknowledge-hold
  "Attach a launch receipt to its gesture. A release preceding the receipt emits
  exactly one end addressed to the launched instance; other gestures are intact."
  [state gesture-id ack]
  (if-let [gesture (get-in state [:gestures gesture-id])]
    (if (and (= :accepted (:status ack)) (:instance-id ack))
      (if (:pressed? gesture)
        {:state (assoc-in state [:gestures gesture-id :instance-id] (:instance-id ack)) :commands []}
        {:state (update state :gestures dissoc gesture-id)
         :commands [(merge (:release-envelope gesture)
                           {:op :instance/end :instance-id (:instance-id ack)})]})
      {:state (update state :gestures dissoc gesture-id) :commands []})
    {:state state :commands []}))

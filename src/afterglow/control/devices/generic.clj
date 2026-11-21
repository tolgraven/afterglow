(ns afterglow.control.devices.generic
  "Generic MIDI, decoded OSC and sensor profiles over the same controls. Port and
  sensor transports are explicit injected resources, never opened on require."
  (:require [afterglow.control.bindings :as bindings]
            [afterglow.control.codecs.midi :as midi]
            [afterglow.control.codecs.osc :as osc]
            [afterglow.control.devices.session :as session]))

(def push-3-capabilities
  {:device :ableton/push-3 :verification :unverified
   :controller-midi {:supported-via :explicit-generic-mapping :automatic-mapping? false}
   :display :unsupported :standalone :unsupported :hardware-verified? false})

(defn- cue-binding [state id binding event envelope]
  (let [pressed? (case (:type event)
                   :note-on true :note-off false
                   (if (contains? event :pressed?) (:pressed? event)
                       (>= (:value event) (get binding :threshold 0.5))))
        gesture (get-in state [:active-gestures id])
        mode (get binding :launch-mode :held)]
    (cond
      (and pressed? gesture) {:state state :commands []}
      pressed?
      (if (= :held mode)
        (let [result (bindings/begin-hold (:holds state) (:cue-id binding) envelope)]
          {:state (-> state (assoc :holds (:state result))
                      (assoc-in [:active-gestures id] (:gesture-id result)))
           :commands (:commands result)})
        {:state (assoc-in state [:active-gestures id] :pressed)
         :commands [{:op :cue/launch :cue-id (:cue-id binding)
                     :launch (assoc (get binding :launch {}) :mode mode)}]})
      (and gesture (= mode :held))
      (let [result (bindings/end-hold (:holds state) gesture envelope)]
        {:state (-> state (assoc :holds (:state result)) (update :active-gestures dissoc id))
         :commands (:commands result)})
      :else {:state (update state :active-gestures dissoc id) :commands []})))

(defn- mapped-input [bindings state event _model envelope]
  (reduce (fn [{:keys [state commands]} [index binding]]
            (let [id (get binding :id index)
                  note-binding? (and (:cue-id binding) (#{:note-on :note-off} (get-in binding [:event :type])))
                  pattern (if note-binding? (dissoc (:event binding) :type) (:event binding))]
              (if (and (or (not note-binding?) (#{:note-on :note-off} (:type event)))
                       (bindings/input-matches? event pattern))
                (let [result (if (:cue-id binding)
                               (cue-binding state id binding event
                                            (assoc envelope :gesture-id (str (:command-id envelope) ":" id)))
                               (let [mapped (bindings/apply-input (get-in state [:controls id] {}) event binding envelope)]
                                 {:state (assoc-in state [:controls id] (:state mapped))
                                  :commands (:commands mapped)}))]
                  {:state (:state result) :commands (into commands (:commands result))})
                {:state state :commands commands})))
          {:state state :commands []} (map-indexed vector bindings)))

(defn profile
  "kind is :midi, :osc or :sensor. MIDI/sensor :bindings use partial :event maps,
  then either standard bindings/apply-input options or :cue-id/:launch-mode.
  Sensor cue bindings support :threshold or explicit event :pressed?. OSC accepts
  decoded {:path :args} messages and explicit :mappings."
  [{:keys [kind bindings mappings] :or {kind :midi bindings [] mappings {}}}]
  (when-not (#{:midi :osc :sensor} kind)
    (throw (ex-info "Unknown generic control transport" {:kind kind})))
  (when-not (and (vector? bindings) (map? mappings))
    (throw (ex-info "Bindings must be a vector and OSC mappings a map" {})))
  {:id kind :initial-state {:controls {} :holds {} :active-gestures {}}
   :decode (if (= kind :midi)
             (fn [raw]
               (cond (map? raw) raw
                     (and (integer? (first raw)) (<= 0x80 (first raw) 0xef)) (midi/decode raw)
                     :else nil)) identity)
   :input (if (= kind :osc)
            (fn [state event _model envelope]
              {:state state :commands (if-let [command (osc/command mappings event envelope)] [command] [])})
            (partial mapped-input bindings))
   :ack (fn [state command ack]
          (if-let [gesture (:gesture-id command)]
            (let [result (bindings/acknowledge-hold (:holds state) gesture ack)]
              {:state (assoc state :holds (:state result)) :commands (:commands result)})
            {:state state}))
   :stop (fn [state _model _envelope _disconnected?]
           {:state {:controls {} :holds {} :active-gestures {}}
            :commands (mapv (fn [id] {:op :instance/end :instance-id id})
                            (keep :instance-id (vals (get-in state [:holds :gestures]))))})})

(defn connect!
  "Connect generic controls. :transport is an injected input transport with the
  session MIDI-style open!/send!/close! interface; sensor send! may be a no-op."
  [{:keys [transport] :as options}]
  (session/open! (session/create (cond-> (assoc options :profile (profile options))
                                  transport (assoc :midi transport)))))

(defn connect-midi! [options] (connect! (assoc options :kind :midi)))
(defn connect-osc! [options] (connect! (assoc options :kind :osc)))
(defn connect-sensor! [options] (connect! (assoc options :kind :sensor)))

(defn connect-push-3-midi!
  "Use a caller-supplied verified generic MIDI map. No Push 2 messages, display
  protocol, identity detection or standalone capability is assumed."
  [options]
  (when-not (seq (:bindings options))
    (throw (ex-info "Push 3 requires an explicit mapping verified for the connected unit/mode"
                    {:capabilities push-3-capabilities})))
  (connect-midi! options))

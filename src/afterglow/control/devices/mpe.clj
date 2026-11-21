(ns afterglow.control.devices.mpe
  "Explicit MPE device session. Pure note ownership and expression mapping use
  the common cue/parameter commands; only session/open! acquires a transport."
  (:require [afterglow.control.bindings :as bindings]
            [afterglow.control.codecs.mpe :as codec]
            [afterglow.control.devices.expressive :as expressive]
            [afterglow.control.devices.session :as session]))

(def capabilities
  {:protocol :midi-1-mpe :axes codec/axes :automatic-schema-mapping? true
   :zone-configuration :explicit :zone-expression :reported-only
   :rpn-negotiation :not-implemented :sustain :not-implemented
   :ambiguous-channel-expression :withheld :hardware-verified? false})

(defn- initial [] {:decoder (codec/initial-state) :voices {} :holds {} :diagnostics []})
(defn- diagnose [state entries]
  (update state :diagnostics #(vec (take-last 32 (into % entries)))))

(defn- cue-id [options model note]
  (or (get (:note-cues options) note)
      (when-let [cell (get (:note-cells options) note)]
        (get-in model [:pages (get options :page-id :main) :cells cell]))
      (:cue-id options)))

(defn- mapped-commands [instance-id values]
  (mapv (fn [[parameter value]] {:op :param/set :instance-id instance-id :param parameter :value value})
        (sort-by (comp str key) values)))

(defn- mapping-plan [options model device-id cue-id schemas]
  (let [defaults (update (:mapping-policy options {}) :params #(merge {} %1 %2 %3)
                         (:param-mappings options) (get-in options [:cue-mappings cue-id]))
        policy (expressive/policy model device-id cue-id defaults)]
    (expressive/plan schemas (:axes options) (:params policy) (dissoc policy :params))))

(defn- note-on [options state event model envelope]
  (let [id (cue-id options model (:note event)) cue (get-in model [:registry :cues id])
        current (get-in model [:registry :effects (:effect-id cue)])
        definition (if-let [version (:effect-version cue)]
                     (or (get-in model [:registry :versions [:effects (:effect-id cue) version]])
                         (when (= version (:version current)) current)) current)]
    (if-not (and cue definition)
      {:state (diagnose state [{:code :unmapped-note :note (:note event) :channel (:channel event)}])}
      (let [device-id (or (:mapping-id options) (:session-id options) (get-in envelope [:source :session-id]))
            plan (mapping-plan options model device-id id (:params definition {}))
            current (merge (into {} (map (fn [[k schema]] [k (:default schema)]) (:params definition)))
                           (:params cue) (:saved-params cue))
            values (expressive/values plan (:axes event) current)
            voice-id (:voice-id event)
            gesture-id (str (:command-id envelope) ":mpe:" (pr-str voice-id))
            hold (bindings/begin-hold (:holds state) id (assoc envelope :gesture-id gesture-id))]
        {:state (-> state (assoc :holds (:state hold) :selected-voice voice-id)
                    (assoc-in [:voices voice-id] {:gesture-id gesture-id :plan plan :pending-values {}
                                                 :cue-id id :device-id device-id :schemas (:params definition)
                                                 :params (merge current values)})
                    (diagnose (:diagnostics plan)))
         :commands (mapv #(-> % (assoc :control/voice-id voice-id)
                              (assoc-in [:launch :params] values)
                              (assoc-in [:launch :velocity] (get-in event [:axes :strike]))) (:commands hold))}))))

(defn- expression [options state voice-id axis-values model]
  (if-let [voice (get-in state [:voices voice-id])]
    (let [instance (get-in model [:instances (:instance-id voice)])
          schemas (if instance (get-in instance [:definition :params]) (:schemas voice))
          plan (mapping-plan options model (:device-id voice) (:cue-id voice) schemas)
          values (expressive/values plan axis-values (or (:params instance) (:params voice)))
          state (-> state (assoc-in [:voices voice-id :plan] plan)
                    (update-in [:voices voice-id :params] merge values))]
      (if (:instance-id voice)
        {:state state :commands (when (= :running (:phase instance)) (mapped-commands (:instance-id voice) values))}
        {:state (update-in state [:voices voice-id :pending-values]
                           #(merge (select-keys % (map :param (:mappings plan))) values))}))
    {:state state}))

(defn- note-off [options state event model envelope]
  (if-let [voice (get-in state [:voices (:voice-id event)])]
    (let [expression (expression options state (:voice-id event) (:axes event) model)
          release (bindings/end-hold (:holds state) (:gesture-id voice) envelope)]
      {:state (cond-> (assoc (:state expression) :holds (:state release))
                (:instance-id voice) (update :voices dissoc (:voice-id event))
                (nil? (:instance-id voice)) (assoc-in [:voices (:voice-id event) :ended?] true))
       :commands (into (vec (:commands expression)) (:commands release))})
    {:state state}))

(defn- input [zone options state bytes model envelope]
  (let [decoded (codec/advance zone (:decoder state) bytes)
        state (-> state (assoc :decoder (:state decoded)) (diagnose (:diagnostics decoded)))]
    (reduce (fn [{:keys [state commands]} event]
              (let [result (case (:type event)
                             :note-on (note-on options state event model envelope)
                             :note-off (note-off options state event model envelope)
                             :axis (expression options state (:voice-id event) {(:axis event) (:value event)} model)
                             :zone-axis {:state (diagnose state [{:code :zone-expression-unmapped
                                                                :axis (:axis event) :channel (:channel event)}])})]
                {:state (:state result) :commands (into commands (:commands result))}))
            {:state state :commands []} (:events decoded))))

(defn- acknowledge [state command ack]
  (if-let [voice-id (:control/voice-id command)]
    (let [voice (get-in state [:voices voice-id])
          held (bindings/acknowledge-hold (:holds state) (:gesture-id command) ack)
          accepted? (and (= :accepted (:status ack)) (:instance-id ack))
          parameters (when (and accepted? voice) (mapped-commands (:instance-id ack) (:pending-values voice)))
          state (cond-> (assoc state :holds (:state held))
                  (and accepted? (= voice-id (:selected-voice state)) (not (:ended? voice)))
                  (assoc :selected-instance (:instance-id ack)))]
      {:state (cond
                (nil? voice) state
                (or (not accepted?) (:ended? voice)) (update state :voices dissoc voice-id)
                :else (assoc-in state [:voices voice-id] (assoc voice :instance-id (:instance-id ack) :pending-values {})))
       :commands (into (vec parameters) (:commands held))})
    {:state state}))

(defn profile
  "Configure :zone, explicit :axes, and :cue-id, :note-cues {note cue-id}, or
  :note-cells {note [x y]} plus :page-id. Every note launches an independently
  held instance. Semantic names and :control/axis supply automatic mappings;
  :param-mappings/:cue-mappings and :mapping-policy provide explicit overrides.
  Persistent [:settings :expressive :devices mapping-id] policies override these
  defaults live. :mapping-id defaults to the session ID; disabling expression
  leaves cue launch/release behavior intact."
  [{:keys [zone axes note-cues note-cells cue-id] :as options}]
  (let [zone (codec/compile-zone zone)]
    (expressive/normalize-policy (:mapping-policy options {}))
    (expressive/normalize-policy {:params (:param-mappings options {})})
    (doseq [[_ bindings] (:cue-mappings options)] (expressive/normalize-policy {:params bindings}))
    (when-not (and (coll? axes) (seq axes) (every? #(contains? codec/axes %) axes)
                   (or cue-id (seq note-cues) (seq note-cells)))
      (throw (ex-info "MPE requires declared axes and an explicit cue/note mapping" {:type ::invalid-options})))
    (doseq [[note id] note-cues]
      (when-not (and (integer? note) (<= 0 note 127) (some? id))
        (throw (ex-info "Invalid MPE note/cue mapping" {:type ::invalid-options :note note}))))
    (doseq [[note cell] note-cells]
      (when-not (and (integer? note) (<= 0 note 127) (vector? cell) (= 2 (count cell))
                     (every? #(and (integer? %) (<= 0 %)) cell))
        (throw (ex-info "Invalid MPE note/page cell mapping" {:type ::invalid-options :note note}))))
    {:id :mpe :capabilities (assoc capabilities :available-axes (select-keys codec/axes axes))
     :initial-state (initial) :decode identity :input (partial input zone options)
     :ack acknowledge :reset-model (fn [_] (initial))
     :stop (fn [state _model _envelope _disconnected?]
             {:state (initial)
              :commands (mapv (fn [id] {:op :instance/end :instance-id id})
                              (distinct (keep :instance-id (vals (get-in state [:holds :gestures])))))})}))

(defn connect! [options]
  (session/open! (session/create (assoc options :profile (profile options)))))

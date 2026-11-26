(ns afterglow.control.devices.x-touch
  "Composable X-Touch/XT MCU profile with explicit transports. Domain writes
  use the shared commands; all banks, holds, touch ownership and feedback diffs
  are passed as data. Physical hardware has not been verified."
  (:require [afterglow.control.bindings :as bindings]
            [afterglow.control.params :as params]
            [afterglow.control.codecs.x-touch :as codec]
            [afterglow.control.devices.session :as session]
            [afterglow.control.devices.transports :as transports]))

(def capabilities
  {:protocol :mcu :verification :source-derived :hardware-verified? false
   :channel-strips 8 :master-fader :main-unit-only :fader-resolution 14
   :scribble-colors 8 :display {:rows 2 :columns 56 :encoding :ascii}
   :color-mixing :research-helper-only :xctl-ethernet :unsupported
   :native-pwm :unverified :compact-and-mini :different-protocol-unverified})

(defn- fail! [message] (throw (ex-info message {:x-touch/error :invalid-profile})))

(defn- initial [bank] {:bank bank :touches {} :holds {} :hold-keys {} :sent {} :flip? false :selected nil :shift? false})

(defn- latest-instance [model cue-id]
  (when cue-id
    (last (sort-by :order (filter #(= cue-id (:cue-id %)) (vals (:instances model)))))))

(defn- control-binding [channel kind]
  (let [entry (get channel kind :level)] (if (keyword? entry) {:param entry} entry)))

(defn- hydrate [model target]
  (if (:master? target)
    (assoc target :schema {:type :number :bounds [0 1] :default 1} :value (:master model))
    (when-let [instance (get-in model [:instances (:instance-id target)])]
      (let [schema (get-in instance [:definition :params (:param target)])
            value (get-in instance [:params (:param target)]) component (:component target)
            component? (and (integer? component) (not= :gradient (:type schema)) (vector? value)
                            (< -1 component (count value)))
            schema (if component? {:type :number :bounds (if (= :color (:type schema)) (params/color-bounds schema) (:bounds schema))
                                   :default (get (:default schema) component)} schema)
            value (if component? (nth value component) value)]
        (when (and schema (or (nil? component) component?)
                   (#{:number :integer :boolean :enum} (:type schema)))
          (assoc target :schema schema :value value :whole-value (get-in instance [:params (:param target)])))))))

(defn- target [model channel kind]
  (when-let [instance (latest-instance model (:cue-id channel))]
    (hydrate model (merge {:instance-id (:id instance)} (control-binding channel kind)))))

(defn- bounds [schema] (or (:bounds schema) [0 1]))

(defn- normalized [target]
  (let [{:keys [schema value]} target [low high] (bounds schema)]
    (case (:type schema)
      (:number :integer) (when (and (number? value) (number? low) (number? high))
                          (if (= low high) 0.0 (bindings/scale value [low high] [0.0 1.0])))
      :boolean (if value 1.0 0.0)
      :enum (let [values (or (:values schema) (:options schema)) index (.indexOf ^java.util.List values value)]
              (when (<= 0 index) (if (< (count values) 2) 0.0 (/ index (double (dec (count values)))))))
      nil)))

(defn- value-at [target normalized]
  (let [schema (:schema target) [low high] (bounds schema)]
    (case (:type schema)
      :number (bindings/scale normalized [0 1] [low high])
      :integer (long (Math/round (double (bindings/scale normalized [0 1] [low high]))))
      :boolean (>= normalized 0.5)
      :enum (let [values (or (:values schema) (:options schema))]
              (nth values (long (Math/round (double (* normalized (dec (count values)))))))))))

(defn- write-command [target value]
  (if (:master? target) {:op :master/set :value value}
    {:op :param/set :instance-id (:instance-id target) :param (:param target)
     :value (if-let [component (:component target)] (assoc (:whole-value target) component value) value)}))

(defn- channels-for [{:keys [channels group-channels]} model]
  (if group-channels (into (vec (group-channels model)) channels) channels))

(defn- current-bank
  "A host-owned bank (:model-bank) is read from the committed model, so every
  unit and every other client sees the same window. Otherwise the session's
  local bank applies."
  [options state model]
  (if-let [model-bank (:model-bank options)]
    (let [bank (model-bank model)] (if (and (integer? bank) (<= 0 bank)) bank 0))
    (:bank state)))

(defn- channel-at [options bank channels strip]
  (get channels (+ bank (:channel-offset options) strip)))

(defn bank-limit
  "Largest first strip of a surface window `width` strips wide over `strip-count`
  strips. Everything fits at 0; otherwise pages stay on multiples of eight, so
  a remainder that does not fill the surface starts on the main unit."
  [strip-count width]
  (if (<= strip-count width) 0 (* 8 (quot (dec strip-count) 8))))

(defn move-bank
  "Next first strip after a bank `move`: :previous/:next by `width`,
  :channel-previous/:channel-next by one, :first or :last. Clamped to
  bank-limit; a stale offset beyond the strips returns to the limit."
  [strip-count width bank move]
  (let [limit (bank-limit strip-count width)
        target (case move
                 :previous (- bank width) :next (+ bank width)
                 :channel-previous (dec bank) :channel-next (inc bank)
                 :first 0 :last limit
                 (fail! "Unknown bank move"))]
    (max 0 (min limit target))))

(def ^:private bank-moves {46 :previous 47 :next 48 :channel-previous 49 :channel-next})

(def ^:private shift-bank-moves {46 :first 47 :last 48 :first 49 :last})

(def shift-note "MCU SHIFT on the main unit (note 46 hex)." 70)

(defn- bank-move [state note]
  ((if (:shift? state) shift-bank-moves bank-moves) note))

(defn- control-kind [state physical]
  (if (:flip? state) ({:fader :encoder :encoder :fader} physical) physical))

(defn- group-target [{:keys [group-id level]}]
  {:group-id group-id :value level :schema {:type :number :bounds [0 1]}})

(defn- fader-target [options state model channel strip]
  (cond
    (= strip 8) (when-not (:extender? options) {:master? true})
    (:group-id channel) (group-target channel)
    :else (target model channel (control-kind state :fader))))

(defn- hydrate-fader [model channels captured]
  (when captured
    (if-let [id (:group-id captured)]
      (some #(when (= id (:group-id %)) (group-target %)) channels)
      (hydrate model captured))))

(defn- release-hold [state strip envelope]
  (if-let [gesture (get-in state [:hold-keys strip])]
    (let [result (bindings/end-hold (:holds state) gesture envelope)]
      {:state (-> state (assoc :holds (:state result)) (update :hold-keys dissoc strip)) :commands (:commands result)})
    {:state state :commands []}))

(defn input
  "Pure interaction -> local state and shared domain command templates. Fader
  touch captures its instance/parameter or group ID across bank changes."
  [options state event model envelope]
  (let [{:keys [type strip pressed? note]} event
        channels (channels-for options model)
        at (partial channel-at options (current-bank options state model) channels)
        channel (when (and (integer? strip) (<= 0 strip 7)) (at strip))
        touched? (contains? (:touches state) strip)
        changed (fn [next-state & commands] {:state next-state :commands (vec commands)})]
    (case type
      :bank/set (do (when-not (and (integer? (:bank event)) (<= 0 (:bank event))) (fail! "Bank must be nonnegative"))
                    (changed (assoc state :bank (:bank event))))
      :touch (cond
               (and pressed? (not touched?))
               ;; An external reconfiguration can arrive before its scribble strip.
               (changed (assoc-in state [:touches strip]
                                  (when (or (not (:group-channels options))
                                            (= (or (:group-id channel) (:cue-id channel))
                                               (get (:shown-channel-ids state) strip)))
                                    (fader-target options state model channel strip))))
               (and (not pressed?) touched?)
               (changed (-> state (update :touches dissoc strip) (update :sent dissoc [:fader strip])))
               :else (changed state))
      :fader (let [captured (if touched? (get-in state [:touches strip])
                               (when-not (or (:require-touch? options) (:group-channels options))
                                 (fader-target options state model channel strip)))
                   selected (hydrate-fader model channels captured)]
               (if selected
                 (let [value (value-at selected (:value event))]
                   (changed state
                            (if-let [id (:group-id selected)]
                              (merge ((:group-level-command options) id value) (select-keys envelope [:show-id :epoch]))
                              (write-command selected value))))
                 (changed state)))
      :encoder (let [selected (target model channel (control-kind state :encoder)) value (when selected (normalized selected))]
                 (if (and (some? value) (not (zero? (:delta event))))
                   (let [schema (:schema selected)
                         step (case (:type schema)
                                :boolean 1.0
                                :enum (/ 1.0 (max 1 (dec (count (or (:values schema) (:options schema))))))
                                :integer (/ 1.0 (max 1 (- (second (bounds schema)) (first (bounds schema)))))
                                (:encoder-step options))
                         adjusted (bindings/clamp (+ value (* step (:delta event))) [0 1])]
                     (changed state (write-command selected (value-at selected adjusted)))) (changed state)))
      :button
      (cond
        (and (not (:extender? options)) (= shift-note note))
        (changed (assoc state :shift? (boolean pressed?)))
        (<= 0 note 7)
        (if pressed?
          (if (get-in state [:hold-keys note]) (changed state)
            (if-let [cue (:cue-id (at note))]
              (let [result (bindings/begin-hold (:holds state) cue envelope)]
                {:state (-> state (assoc :holds (:state result)) (assoc-in [:hold-keys note] (:gesture-id result)))
                 :commands (:commands result)}) (changed state)))
          (release-hold state note envelope))
        (not pressed?) (changed state)
        (<= 24 note 31)
        (let [cue (:cue-id (at (- note 24))) instance (latest-instance model cue)]
          (cond instance (changed state {:op :instance/end :instance-id (:id instance) :force? (= :releasing (:phase instance))})
                cue (changed state {:op :cue/launch :cue-id cue :launch {:mode :persistent}})
                :else (changed state)))
        (<= 16 note 23)
        (if-let [instance (latest-instance model (:cue-id (at (- note 16))))]
          (changed state {:op :instance/end :instance-id (:id instance)}) (changed state))
        (<= 8 note 15) (changed (assoc state :selected (:cue-id (at (- note 8)))))
        (<= 32 note 39)
        (if-let [selected (target model (at (- note 32)) (control-kind state :encoder))]
          (if (some? (get-in selected [:schema :default]))
            (changed state (write-command selected (get-in selected [:schema :default]))) (changed state)) (changed state))
        (and (not (:extender? options)) (bank-moves note))
        (let [move (bank-move state note)]
          (if-let [bank-command (:bank-command options)]
            (changed state (merge (bank-command move) (select-keys envelope [:show-id :epoch])))
            (changed (update state :bank #(move-bank (count channels) (:bank-step options) % move)))))
        (and (not (:extender? options)) (= 50 note)) (changed (update state :flip? not))
        (and (not (:extender? options)) (#{93 94} note)) (changed state {:op :transport/set :transport {:playing? (= note 94)}})
        :else (changed state))
      (changed state))))

(defn- slot-text [value]
  (let [value (str (or value ""))] (str (subs value 0 (min 6 (count value))) (apply str (repeat (max 0 (- 7 (min 6 (count value)))) " ")))))

(defn- display-value [target]
  (let [value (:value target)] (cond (nil? value) "" (number? value) (format "%.3f" (double value)) :else (str value))))

(defn project
  "Pure strip projection. Categories can supply :color in channel metadata;
  transport encoding and IO do not belong to the shared show model."
  [options state model]
  (let [channels (channels-for options model)
        bank (current-bank options state model)]
    (mapv (fn [strip]
            (let [{:keys [cue-id group-id] :as channel} (channel-at options bank channels strip)
                  cue (get-in model [:registry :cues cue-id])
                  instance (when cue-id (latest-instance model cue-id))
                  fader (fader-target options state model channel strip)
                  encoder (when cue-id (target model channel (control-kind state :encoder)))]
              (cond-> {:label (or (:label channel) (:name cue) (some-> cue-id name) "")
                       :color (if channel (codec/palette-index (or (:color channel) [1 1 1])) 0)
                       :active? (if group-id (boolean (:active? channel)) (boolean instance))
                       :held? (contains? (:hold-keys state) strip)
                       :selected? (and cue-id (= (:selected state) cue-id))
                       :fader (when fader (normalized fader)) :encoder (when encoder (normalized encoder))
                       :value-label (display-value fader)}
                group-id (assoc :group-id group-id)
                cue-id (assoc :cue-id cue-id)))) (range 8))))

(defn feedback [options state model _envelope]
  (let [view (project options state model) extender? (:extender? options)
        desired (into {[:text 0] (codec/text extender? 0 0 (apply str (map #(slot-text (:label %)) view)))
                       [:text 1] (codec/text extender? 1 0 (apply str (map #(slot-text (:value-label %)) view)))
                       :colors (codec/colors extender? (mapv :color view))}
                      (mapcat (fn [[strip {:keys [fader encoder active? held? selected?]}]]
                                (concat
                                 (when (and (some? fader) (not (contains? (:touches state) strip)))
                                   [[[:fader strip] (codec/fader strip fader)]])
                                 [[[:ring strip] (codec/encoder-ring strip (if (some? encoder) (inc (long (Math/round (double (* 10 encoder))))) 0))]
                                  [[:led strip] (codec/button-led strip (if held? :on :off))]
                                  [[:led (+ 8 strip)] (codec/button-led (+ 8 strip) (if selected? :on :off))]
                                  [[:led (+ 16 strip)] (codec/button-led (+ 16 strip) (if active? :on :off))]
                                  [[:led (+ 24 strip)] (codec/button-led (+ 24 strip) (if active? :on :off))]]))
                              (map-indexed vector view)))
        desired (cond-> desired
                  (and (not extender?) (not (contains? (:touches state) 8))) (assoc [:fader 8] (codec/fader 8 (:master model)))
                  (not extender?) (assoc [:led 94] (codec/button-led 94 (if (get-in model [:transport :playing?]) :on :off))))
        messages (mapv val (filter (fn [[key message]] (not= message (get-in state [:sent key]))) (sort-by (comp pr-str key) desired)))]
    {:state (cond-> (update state :sent merge desired)
              (:group-channels options) (assoc :shown-channel-ids (mapv #(or (:group-id %) (:cue-id %)) view)))
     :commands [] :midi messages}))

(defn profile
  "Options :channels [{:cue-id :label :color [r g b] :fader binding :encoder binding}],
  where binding is a parameter keyword or {:param :component?}. Main/XT strips
  use :channel-offset plus a bank. A host can prepend stable group strips via
  pure :group-channels (model -> [{:group-id :label :color :level :active?}])
  and :group-level-command (group-id, value -> host command template).
  Profiles with group strips require touch for all faders. Flip and encoders
  apply to cue strips.

  A host that owns the bank supplies :model-bank (model -> first strip) and
  :bank-command (move -> host command template). The main unit then sends
  bank/channel buttons as moves (:previous :next :channel-previous
  :channel-next, or :first/:last with SHIFT) instead of changing its own bank;
  every unit reads the committed bank on its next input or feedback."
  [options]
  (let [options (merge {:channels [] :extender? false :channel-offset 0 :bank 0 :bank-step 8
                        :encoder-step 0.01 :require-touch? true} options)]
    (when-not (and (vector? (:channels options)) (every? map? (:channels options))
                   (every? #(and (integer? %) (<= 0 %)) ((juxt :channel-offset :bank) options))
                   (and (integer? (:bank-step options)) (pos? (:bank-step options)))
                   (boolean? (:extender? options)) (boolean? (:require-touch? options))
                   (or (every? nil? ((juxt :group-channels :group-level-command) options))
                       (every? ifn? ((juxt :group-channels :group-level-command) options)))
                   (or (every? nil? ((juxt :model-bank :bank-command) options))
                       (every? ifn? ((juxt :model-bank :bank-command) options)))
                   (number? (:encoder-step options)) (< 0 (:encoder-step options) 1))
      (fail! "Invalid X-Touch profile options"))
    (doseq [channel (:channels options)]
      (when-not (or (keyword? (:cue-id channel))
                    (and (string? (:cue-id channel)) (seq (:cue-id channel))))
        (fail! "Each channel needs a stable cue ID"))
      (when (:color channel) (codec/palette-index (:color channel)))
      (doseq [kind [:fader :encoder] :let [entry (control-binding channel kind)]]
        (when-not (and (map? entry) (keyword? (:param entry))
                       (or (nil? (:component entry)) (and (integer? (:component entry)) (<= 0 (:component entry)))))
          (fail! "Controls need a parameter key and optional nonnegative component"))))
    {:id (if (:extender? options) :x-touch-xt :x-touch)
     :capabilities (assoc capabilities :extender? (:extender? options))
     :unique-command-prefix? (boolean (or (:group-channels options) (:bank-command options)))
     :fence-captured-commands? (boolean (:group-channels options))
     :initial-state (initial (:bank options))
     :decode #(if (map? %) % (codec/decode %))
     :start (partial feedback options)
     :input (partial input options)
     :feedback (partial feedback options)
     :ack (fn [state command ack]
            (if-let [gesture (:gesture-id command)]
              (let [result (bindings/acknowledge-hold (:holds state) gesture ack)]
                {:state (assoc state :holds (:state result)) :commands (:commands result)})
              {:state state :commands []}))
     :stop (fn [state _model _envelope disconnected?]
             {:state (initial (:bank state))
              :commands (mapv #(hash-map :op :instance/end :instance-id %)
                              (keep :instance-id (vals (get-in state [:holds :gestures]))))
              :midi (if disconnected? [] [(codec/colors (:extender? options) (vec (repeat 8 0)))
                                          (codec/text (:extender? options) 0 0 (apply str (repeat 56 " ")))
                                          (codec/text (:extender? options) 1 0 (apply str (repeat 56 " ")))])})}))

(defn connect!
  "Explicit MCU connection. Supply normal session :model!/:dispatch!/:now-ms!,
  session-id and selected MIDI indices, or an injected :transport. Optional
  :schedule! owns feedback cadence; set nil to refresh manually in tests/hosts."
  [options]
  (let [options (if (contains? options :schedule!) options
                 (assoc options :schedule! (transports/scheduler (get options :refresh-ms 40))))
        current-bank (::current-bank options)
        base-profile (profile options)
        profile (cond-> base-profile
                  current-bank (assoc :start (fn [state model envelope]
                                               ((:start base-profile) (assoc state :bank (current-bank)) model envelope))
                                      :reset-model #(initial (:bank %))))]
    (session/open!
     (session/create (assoc options :profile profile
                            :midi (or (:transport options) (transports/midi-transport options)))))))

(defn set-bank!
  "Set the same logical bank across explicit sessions, preserving each unit's
  channel offset. Caller serializes group interaction; never mutates the model."
  [sessions bank]
  (doseq [device sessions] (session/receive! device {:type :bank/set :bank bank}))
  bank)

(defn group-status
  "Shared bank and each unit's session ID, physical offset, role and status."
  [group]
  (let [{:keys [bank closed? sessions]} @(:state group)]
    {:bank bank :closed? closed?
     :units (mapv #(merge (select-keys (:options %) [:session-id :channel-offset])
                          {:extender? (boolean (get-in % [:options :extender?]))}
                          (select-keys (session/snapshot %) [:status :generation :epoch :errors]))
                  sessions)}))

(defn bank-group!
  "Explicit shared bank change for one main unit and its extenders. Ordered
  unit offsets stay stable. The group owner serializes input; effect state is
  still exclusively in the shared show coordinator."
  [group bank]
  (when-not (and (integer? bank) (<= 0 bank)) (fail! "Bank must be nonnegative"))
  (locking (:lock group)
    (when (:closed? @(:state group)) (fail! "X-Touch group is closed"))
    (swap! (:state group) assoc :bank bank)
    (set-bank! (:sessions @(:state group)) bank))
  (group-status group))

(defn- unit-session [group session-id]
  (or (some #(when (= session-id (get-in % [:options :session-id])) %) (:sessions @(:state group)))
      (fail! "No unit with that session ID in this X-Touch group")))

(defn close-unit!
  "Close one unit of an open group (for example an unplugged extender). The
  other units keep their offsets and the shared bank. Held cues on that unit
  are released as for any closed session."
  [group session-id]
  (locking (:lock group)
    (when (:closed? @(:state group)) (fail! "X-Touch group is closed"))
    (session/close! (unit-session group session-id)))
  (group-status group))

(defn reopen-unit!
  "Reopen one closed unit at its original offset and the group's current bank."
  [group session-id]
  (locking (:lock group)
    (when (:closed? @(:state group)) (fail! "X-Touch group is closed"))
    (let [device (unit-session group session-id)]
      (session/open! device)
      (session/receive! device {:type :bank/set :bank (:bank @(:state group))})))
  (group-status group))

(defn close-group! [group]
  (let [sessions (locking (:lock group)
                   (let [state @(:state group)]
                     (when-not (:closed? state)
                       (reset! (:state group) (assoc state :closed? true :sessions []))
                       (:sessions state))))]
    (doseq [device (reverse sessions)] (session/close! device))
    (group-status group)))

(defn- group-transport [group unit-session options]
  (let [{:keys [extender? bank-step model! bank-command]} options
        transport (or (:transport options) (transports/midi-transport options))
        current-open (volatile! nil)]
    (assoc transport
           :open! (fn [receive!]
                    (let [opened (vreset! current-open (Object.))]
                      ((:open! transport)
                       (fn [raw]
                         (locking (:lock group)
                           (when (and (identical? opened @current-open) (not (:closed? @(:state group))))
                             (let [{:keys [type pressed? note]} (if (map? raw) raw
                                                                  (try (codec/decode raw) (catch Exception _ nil)))
                                   ;; A host-owned bank goes through the main profile's command.
                                   move? (and (not extender?) (not bank-command) (= :button type) pressed? (bank-moves note))]
                               (if move?
                                 (when-let [snapshot (some-> @unit-session session/snapshot)]
                                   (when (= :active (:status snapshot))
                                     (bank-group! group (move-bank (count (channels-for options (model!))) bank-step
                                                                   (:bank @(:state group)) (bank-move (:local snapshot) note)))))
                                 (receive! raw)))))))))
           :close! (fn [handle]
                     (vreset! current-open nil)
                     ((:close! transport) handle)))))

(defn connect-group!
  "Open an explicitly ordered vector of :units, exactly one main and any
  extenders. Each unit has its own :session-id, selected ports/:transport and
  :extender? flag. Common :channels/model!/dispatch!/now-ms! are shared options.
  Bank buttons on the main move the whole group; channel buttons move one slot;
  with SHIFT held either pair jumps to the first or last bank. With
  :model-bank/:bank-command (see profile) the host owns the bank instead and
  the group never changes it. close-unit!/reopen-unit! handle one unit.
  No discovery/automatic port pairing or shared global state is introduced."
  [{:keys [units channels] :as options}]
  (when-not (and (vector? units) (<= 1 (count units) 16)
                 (= 1 (count (remove :extender? units)))
                 (= (count units) (count (set (map :session-id units))))
                 (every? #(and (string? (:session-id %)) (seq (:session-id %))) units)
                 (vector? channels))
    (fail! "An ordered group needs unique session IDs and exactly one main unit"))
  (let [width (* 8 (count units))
        group {:lock (Object.) :state (atom {:bank (get options :bank 0) :closed? false :sessions []})}]
    (try
      (doseq [[index unit] (map-indexed vector units)]
        (let [settings (merge (dissoc options :units) unit
                              {:channel-offset (* 8 index) :bank-step width :bank (:bank @(:state group))
                               ::current-bank #(:bank @(:state group))})
              unit-session (volatile! nil)
              device (connect! (assoc settings :transport (group-transport group unit-session settings)))]
          (locking (:lock group)
            (vreset! unit-session device)
            (swap! (:state group) update :sessions conj device)
            (session/receive! device {:type :bank/set :bank (:bank @(:state group))}))))
      group
      (catch Throwable error (close-group! group) (throw error)))))

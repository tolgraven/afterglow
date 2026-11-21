(ns afterglow.control.devices.x-touch
  "Composable X-Touch/XT MCU profile with explicit transports. Domain writes
  use the shared commands; all banks, holds, touch ownership and feedback diffs
  are passed as data. Physical hardware has not been verified."
  (:require [afterglow.control.bindings :as bindings]
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
(defn- initial [bank] {:bank bank :touches {} :holds {} :hold-keys {} :sent {} :flip? false :selected nil})
(defn- latest-instance [model cue-id]
  (last (sort-by :order (filter #(= cue-id (:cue-id %)) (vals (:instances model))))))
(defn- control-binding [channel kind]
  (let [entry (get channel kind :level)] (if (keyword? entry) {:param entry} entry)))

(defn- hydrate [model target]
  (if (:master? target)
    (assoc target :schema {:type :number :bounds [0 1] :default 1} :value (:master model))
    (when-let [instance (get-in model [:instances (:instance-id target)])]
      (let [schema (get-in instance [:definition :params (:param target)])
            value (get-in instance [:params (:param target)]) component (:component target)
            component? (and (integer? component) (vector? value) (< -1 component (count value)))
            schema (if component? {:type :number :bounds (if (= :color (:type schema)) [0 1] (:bounds schema))
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

(defn- channel-at [options state strip]
  (get (:channels options) (+ (:bank state) (:channel-offset options) strip)))
(defn- control-kind [state physical]
  (if (:flip? state) ({:fader :encoder :encoder :fader} physical) physical))

(defn- release-hold [state strip envelope]
  (if-let [gesture (get-in state [:hold-keys strip])]
    (let [result (bindings/end-hold (:holds state) gesture envelope)]
      {:state (-> state (assoc :holds (:state result)) (update :hold-keys dissoc strip)) :commands (:commands result)})
    {:state state :commands []}))

(defn input
  "Pure interaction -> local state and shared domain command templates. Fader
  touch captures its instance/parameter, so banking cannot steal an active touch."
  [options state event model envelope]
  (let [{:keys [type strip pressed? note]} event
        channel (when (and (integer? strip) (< strip 8)) (channel-at options state strip))
        changed (fn [next-state & commands] {:state next-state :commands (vec commands)})]
    (case type
      :bank/set (do (when-not (and (integer? (:bank event)) (<= 0 (:bank event))) (fail! "Bank must be nonnegative"))
                    (changed (assoc state :bank (:bank event))))
      :touch (let [captured (if (and (= strip 8) (not (:extender? options))) {:master? true}
                               (target model channel (control-kind state :fader)))]
               (changed (if pressed? (assoc-in state [:touches strip] captured) (update state :touches dissoc strip))))
      :fader (let [touched? (contains? (:touches state) strip)
                   selected (if touched? (get-in state [:touches strip])
                              (when-not (:require-touch? options)
                                (if (and (= strip 8) (not (:extender? options))) {:master? true}
                                  (target model channel (control-kind state :fader)))))
                   selected (when selected (hydrate model selected))]
               (if (and selected (or touched? (not (:require-touch? options))))
                 (changed state (write-command selected (value-at selected (:value event)))) (changed state)))
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
        (<= 0 note 7)
        (if pressed?
          (if (get-in state [:hold-keys note]) (changed state)
            (if-let [cue (:cue-id (channel-at options state note))]
              (let [result (bindings/begin-hold (:holds state) cue envelope)]
                {:state (-> state (assoc :holds (:state result)) (assoc-in [:hold-keys note] (:gesture-id result)))
                 :commands (:commands result)}) (changed state)))
          (release-hold state note envelope))
        (not pressed?) (changed state)
        (<= 24 note 31)
        (let [cue (:cue-id (channel-at options state (- note 24))) instance (latest-instance model cue)]
          (cond instance (changed state {:op :instance/end :instance-id (:id instance) :force? (= :releasing (:phase instance))})
                cue (changed state {:op :cue/launch :cue-id cue :launch {:mode :persistent}})
                :else (changed state)))
        (<= 16 note 23)
        (if-let [instance (latest-instance model (:cue-id (channel-at options state (- note 16))))]
          (changed state {:op :instance/end :instance-id (:id instance)}) (changed state))
        (<= 8 note 15) (changed (assoc state :selected (:cue-id (channel-at options state (- note 8)))))
        (<= 32 note 39)
        (if-let [selected (target model (channel-at options state (- note 32)) (control-kind state :encoder))]
          (if (some? (get-in selected [:schema :default]))
            (changed state (write-command selected (get-in selected [:schema :default]))) (changed state)) (changed state))
        (and (not (:extender? options)) (#{46 47 48 49} note))
        (let [delta ({46 (- (:bank-step options)) 47 (:bank-step options) 48 -1 49 1} note)
              maximum (max 0 (* 8 (quot (dec (max 1 (count (:channels options)))) 8)))]
          (changed (update state :bank #(max 0 (min maximum (+ % delta))))))
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
  (mapv (fn [strip]
          (let [channel (channel-at options state strip) cue (get-in model [:registry :cues (:cue-id channel)])
                instance (latest-instance model (:cue-id channel))
                fader (target model channel (control-kind state :fader)) encoder (target model channel (control-kind state :encoder))]
            {:label (or (:label channel) (:name cue) (some-> (:cue-id channel) name) "")
             :color (if channel (codec/palette-index (or (:color channel) [1 1 1])) 0)
             :active? (boolean instance) :held? (contains? (:hold-keys state) strip)
             :selected? (and channel (= (:selected state) (:cue-id channel)))
             :fader (when fader (normalized fader)) :encoder (when encoder (normalized encoder))
             :value-label (display-value fader)})) (range 8)))

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
    {:state (update state :sent merge desired) :commands [] :midi messages}))

(defn profile
  "Options :channels [{:cue-id :label :color [r g b] :fader binding :encoder binding}],
  where binding is a parameter keyword or {:param :component?}. Main/XT strips
  use :channel-offset plus a bank. Touch-gated faders are the default; no motor
  echo is interpreted as an intentional parameter edit. No global mutable state."
  [options]
  (let [options (merge {:channels [] :extender? false :channel-offset 0 :bank 0 :bank-step 8
                        :encoder-step 0.01 :require-touch? true} options)]
    (when-not (and (vector? (:channels options)) (every? map? (:channels options))
                   (every? #(and (integer? %) (<= 0 %)) ((juxt :channel-offset :bank) options))
                   (and (integer? (:bank-step options)) (pos? (:bank-step options)))
                   (boolean? (:extender? options)) (boolean? (:require-touch? options))
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
                 (assoc options :schedule! (transports/scheduler (get options :refresh-ms 40))))]
    (session/open!
     (session/create (assoc options :profile (profile options)
                            :midi (or (:transport options) (transports/midi-transport options)))))))

(defn set-bank!
  "Set the same logical bank across explicit sessions, preserving each unit's
  channel offset. Caller serializes group interaction; never mutates the model."
  [sessions bank]
  (doseq [device sessions] (session/receive! device {:type :bank/set :bank bank}))
  bank)

(defn group-status [group]
  (let [{:keys [bank closed? sessions]} @(:state group)]
    {:bank bank :closed? closed?
     :units (mapv #(select-keys (session/snapshot %) [:status :generation :epoch :errors]) sessions)}))

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

(defn close-group! [group]
  (let [sessions (locking (:lock group)
                   (let [state @(:state group)]
                     (when-not (:closed? state)
                       (reset! (:state group) (assoc state :closed? true :sessions []))
                       (:sessions state))))]
    (doseq [device (reverse sessions)] (session/close! device))
    (group-status group)))

(defn connect-group!
  "Open an explicitly ordered vector of :units, exactly one main and any
  extenders. Each unit has its own :session-id, selected ports/:transport and
  :extender? flag. Common :channels/model!/dispatch!/now-ms! are shared options.
  Bank buttons on the main move the whole group; channel buttons move one slot.
  No discovery/automatic port pairing or shared global state is introduced."
  [{:keys [units channels] :as options}]
  (when-not (and (vector? units) (<= 1 (count units) 16)
                 (= 1 (count (remove :extender? units)))
                 (= (count units) (count (set (map :session-id units))))
                 (every? #(and (string? (:session-id %)) (seq (:session-id %))) units)
                 (vector? channels))
    (fail! "An ordered group needs unique session IDs and exactly one main unit"))
  (let [width (* 8 (count units))
        group {:lock (Object.) :state (atom {:bank (get options :bank 0) :closed? false :sessions []})}
        maximum (max 0 (* 8 (quot (dec (max 1 (count channels))) 8)))]
    (try
      (doseq [[index unit] (map-indexed vector units)]
        (let [settings (merge (dissoc options :units) unit
                              {:channel-offset (* 8 index) :bank-step width :bank (:bank @(:state group))})
              transport (or (:transport settings) (transports/midi-transport settings))
              wrapped (assoc transport :open!
                             (fn [receive!]
                               ((:open! transport)
                                (fn [raw]
                                  (locking (:lock group)
                                    (when-not (:closed? @(:state group))
                                      (let [event (if (map? raw) raw
                                                    (try (codec/decode raw) (catch Exception _ nil)))]
                                        (if (and (not (:extender? settings)) (= :button (:type event))
                                                 (:pressed? event) (#{46 47 48 49} (:note event)))
                                          (let [delta ({46 (- width) 47 width 48 -1 49 1} (:note event))]
                                            (bank-group! group (max 0 (min maximum (+ (:bank @(:state group)) delta)))))
                                          (receive! raw)))))))))
              device (connect! (assoc settings :transport wrapped))]
          (locking (:lock group)
            (swap! (:state group) update :sessions conj device)
            (session/receive! device {:type :bank/set :bank (:bank @(:state group))}))))
      group
      (catch Throwable error (close-group! group) (throw error)))))

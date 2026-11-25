(ns afterglow.control.devices.push-3
  "Push 3 User Mode controls over the shared semantic model. Addresses are
  captured explicitly. An optional tethered display consumes the shared Push view."
  (:require [afterglow.control.bindings :as bindings]
            [afterglow.control.codecs.push-3 :as codec]
            [afterglow.control.codecs.mpe :as mpe-codec]
            [afterglow.control.devices.encoder-gesture :as encoder-gesture]
            [afterglow.control.devices.mpe :as mpe]
            [afterglow.control.devices.push-cue-gesture :as gesture]
            [afterglow.control.devices.push-launch :as launch]
            [afterglow.control.devices.push-view :as push-view]
            [afterglow.control.devices.session :as session]
            [afterglow.control.devices.transports :as transports]
            [afterglow.control.display :as display]
            [afterglow.control.devices.target-picker :as targets]
            [afterglow.control.pages :as pages]
            [afterglow.control.params :as params]
            [afterglow.control.parameter-edit :as edit]
            [afterglow.control.views :as views]))

(def capabilities
  (assoc codec/capabilities :adapter :composable-session
         :controls #{:pad-cues :held-release :parameter-encoders :master-encoder
                     :parameter-pressure :parameter-touch-strip :page-scroll
                     :manual-handoff :reconnect :shift-fine}
         :feedback :semantic-view :display-protocol :tethered-descriptor-replay))

(defn- valid! [condition message data]
  (when-not condition (throw (ex-info message (assoc data :type ::invalid-options)))))

(defn- reset-interactions [state]
  (assoc (dissoc (targets/clear-selection state) :encoder-gestures :encoder-releases :encoder-touch-modes
                 :temporary-release-tails :temporary-release-time-ms)
         :pads {} :holds {} :buttons #{} :dedicated-modifier-down? false :touches #{}
         :selected-instance nil :selected-cue nil :selection-token nil :shift-patch nil :last-display nil))

(defn- cue-at [state model [x y]]
  (let [[left bottom] (:origin state)
        id (pages/cue-id-at model (:page-id state) [(+ left x) (+ bottom y)])]
    (get-in model [:registry :cues id])))

(defn- release-pad [state key envelope]
  (if-let [pad (get-in state [:pads key])]
    (let [release (when-let [gesture (:gesture-id pad)]
                    (bindings/end-hold (:holds state) gesture envelope))]
      {:state (cond-> (update state :pads dissoc key) release (assoc :holds (:state release)))
       :commands (:commands release)})
    {:state state}))

(defn- press-pad [options state event model envelope]
  (let [key (:gesture-key event)]
    (if (get-in state [:pads key])
      {:state state}
      (if-let [cue (cue-at state model (:control-id event))]
        (let [mode (or (:launch-mode options) (:launch-mode cue) (when (:held cue) :held) :persistent)
              token (:command-id envelope)
              active (last (filter #(= (:id cue) (:cue-id %)) (views/active-instances model)))
              state (-> state
                        (assoc :selected-cue (:id cue) :selection-token token
                               :selected-instance nil)
                        (assoc-in [:pads key] {:token token :mode mode}))
              metadata {:control/pad-key key :control/selection-token token}]
          (cond
            (= mode :held)
            (let [hold (bindings/begin-hold (:holds state) (:id cue) envelope (::grid options))]
              {:state (-> state (assoc :holds (:state hold))
                          (assoc-in [:pads key :gesture-id] (:gesture-id hold)))
               :commands (mapv #(-> (merge % metadata)
                                    (assoc-in [:launch :velocity] (:value event))) (:commands hold))})
            (and (= mode :persistent) active (nil? (:target-once state)))
            {:state (-> state (assoc :selected-instance (:id active))
                        (assoc-in [:pads key :instance-id] (:id active)))
             :commands [{:op :instance/end :instance-id (:id active)
                         :force? (= :releasing (:phase active))}]}
            :else
            {:state state :commands [(merge metadata {:op :cue/launch :cue-id (:id cue)
                                                      :launch {:mode mode :velocity (:value event)}})]}))
        ;; Remember presses on empty cells too. A subsequent page edit must not
        ;; turn a repeated pressure-like note-on into an unintended launch.
        {:state (assoc-in state [:pads key] {:mode :empty})}))))

(defn- numeric-parameter [model instance-id parameter]
  (let [instance (get-in model [:instances instance-id])
        schema (get-in instance [:definition :params parameter])
        value (get-in instance [:params parameter])]
    (when (and instance (= :running (:phase instance))
               (#{:number :integer} (:type schema)) (:bounds schema)
               (params/finite-number? value))
      {:instance instance :schema schema :value value})))

(defn- parameter-command [model instance-id parameter transform]
  (when-let [{:keys [schema value]} (numeric-parameter model instance-id parameter)]
    (let [next-value (bindings/clamp (transform value (:bounds schema) schema) (:bounds schema))
          next-value (if (= :integer (:type schema)) (long (Math/round (double next-value))) next-value)]
      (when (not= value next-value)
        {:op :param/set :instance-id instance-id :param parameter :value next-value}))))

(defn- shift-held? [options state]
  (some #(= :shift (get-in options [:button-bindings %])) (:buttons state)))

(defn- temporary-modifier-held? [{:keys [temporary-encoder-modifier] :as options} state]
  (if (= :shift temporary-encoder-modifier)
    (shift-held? options state)
    (:dedicated-modifier-down? state)))

(defn- release-encoder [state control-id time-ms]
  (let [mode (get-in state [:encoder-touch-modes control-id])
        touched? (contains? (:touches state) control-id)
        state (cond-> (update state :touches disj control-id)
                mode (update :encoder-touch-modes dissoc control-id)
                (= :temporary mode) (encoder-gesture/start-temporary-tail control-id time-ms))]
    (encoder-gesture/release state control-id time-ms touched?)))

(defn- touch-encoder [options state {:keys [control-id pressed?]} model envelope]
  (let [mode (get-in state [:encoder-touch-modes control-id])
        touched? (or (contains? (:touches state) control-id) (= :temporary mode))]
    (cond
      (= pressed? touched?) {:state state}
      (not pressed?) (release-encoder state control-id (:time-ms envelope))
      :else
      (let [{:keys [param]} (get-in options [:encoder-bindings control-id])
            instance-id (:selected-instance state)
            temporary? (and param (temporary-modifier-held? options state))
            state (cond-> (update state :touches conj control-id)
                    (and param (:temporary-encoder-modifier options))
                    (assoc-in [:encoder-touch-modes control-id] (if temporary? :temporary :ordinary))
                    (contains? (:temporary-release-tails state) control-id)
                    (update :temporary-release-tails dissoc control-id))]
        (if (and (:operator-gestures? options) param (numeric-parameter model instance-id param))
          (encoder-gesture/start state control-id
                                 {:instance-id instance-id :param param :encoder control-id}
                                 envelope (boolean temporary?))
          {:state state})))))

(defn- turn-parameter [state model instance-id param step delta fine?]
  (if-not fine?
    (let [command (parameter-command model instance-id param
                    (fn [value [low high] schema]
                      (+ value (* delta (or step (if (= :integer (:type schema)) 1 (/ (- high low) 100.0)))))))]
      {:state state :commands (if command [command] [])})
    (if-let [{:keys [instance schema value]} (numeric-parameter model instance-id param)]
      (let [[cache bits] (edit/patch-step (:shift-patch state) model instance param)
            schema (cond-> schema step (assoc :step step))
            next-value (edit/edit schema value delta {:fine? true :dmx-bits bits})]
        {:state (assoc state :shift-patch cache)
         :commands (if (= value next-value) [] [{:op :param/set :instance-id instance-id :param param :value next-value}])})
      {:state state})))

(defn- encoder [options state {:keys [control-id delta]} model envelope]
  (let [{:keys [target param step]} (get-in options [:encoder-bindings control-id])
        fine? (boolean (shift-held? options state))
        active (encoder-gesture/active state control-id)
        mode (get-in state [:encoder-touch-modes control-id])]
    (cond
      (zero? delta) {:state state}
      (= target :master)
      (let [increment (or step 0.01) value (bindings/clamp (+ (:master model) (* delta (if fine? (/ increment 10) increment))) [0 1])]
        {:state state :commands (if (= value (:master model)) [] [{:op :master/set :value value}])})
      active (encoder-gesture/edit state active
               #(turn-parameter state model (:instance-id active) (:param active) step delta fine?))
      (or (= :temporary mode)
          (and (nil? mode) (temporary-modifier-held? options state))
          (contains? (:temporary-release-tails state) control-id)
          (encoder-gesture/after-release? state control-id (:time-ms envelope))) {:state state}
      :else (turn-parameter state model (:selected-instance state) param step delta fine?))))

(defn- expression [options state event model]
  (let [poly? (= :poly-pressure (:type event))
        enabled? (case (:type event)
                   :poly-pressure (= :poly-aftertouch (:expression-mode options))
                   :mono-pressure (= :mono-aftertouch (:expression-mode options))
                   :touch-strip true)
        parameter (get options (if (= :touch-strip (:type event)) :touch-strip-param :pressure-param))
        instance-id (if poly? (get-in state [:pads (:gesture-key event) :instance-id])
                       (:selected-instance state))
        command (when (and enabled? parameter instance-id)
                  (parameter-command model instance-id parameter
                    (fn [_ bounds _] (bindings/scale (:value event) [0 1] bounds))))]
    {:state state :commands (if command [command] [])}))

(defn- set-held-button [options state id down?]
  (if (= id (::dedicated-modifier options))
    (assoc state :dedicated-modifier-down? down?)
    (cond-> (update state :buttons (if down? conj disj) id)
      (and (not down?) (= :shift (get-in options [:button-bindings id]))) (dissoc :shift-patch))))

(defn- button [options state event model]
  (let [id (:control-id event) down? (:pressed? event)
        previously-down? (contains? (:buttons state) id)
        state (set-held-button options state id down?)
        [x y] (:origin state)]
    (if (and down? (not previously-down?) (not= id (::dedicated-modifier options)))
      (let [action (get-in options [:button-bindings id])]
        (if (display/action? action) {:state (display/apply-action state model action)}
        (case action
        :blackout {:state state :commands [{:op :blackout/set :value (not (:blackout? model))}]}
        :transport {:state state :commands [{:op :transport/set :transport {:playing? (not (get-in model [:transport :playing?]))}}]}
        :target-picker {:state (targets/toggle state (:target-search options) model)}
        :page-left {:state (if (:target-picker state) (targets/page state -1) (assoc state :origin [(max 0 (- x 8)) y]))}
        :page-right {:state (if (:target-picker state) (targets/page state 1) (assoc state :origin [(+ x 8) y]))}
        :page-up {:state (assoc state :origin [x (+ y 8)])}
        :page-down {:state (assoc state :origin [x (max 0 (- y 8))])}
        :suspend {:state state :lifecycle :suspend}
        {:state state})))
      {:state state})))

(defn- input [options state event model envelope]
  (let [state (encoder-gesture/observe-temporary-tails state (:time-ms envelope))]
    (case (:type event)
      :pad (let [key (:gesture-key event)]
             (cond
               (contains? (:picker-pads state) key)
               {:state (if (:pressed? event) state (targets/release-pad state key))}
               (not (:pressed? event)) (release-pad state key envelope)
               (:target-picker state) {:state (targets/pad state key (:control-id event))}
               :else (targets/launch state (press-pad options state event model envelope))))
      :encoder (encoder options state event model envelope)
      :encoder-touch (touch-encoder options state event model envelope)
      (:poly-pressure :mono-pressure :touch-strip) (expression options state event model)
      :button (button options state event model)
      {:state state})))

(defn- gesture-result [state result]
  (let [next-gesture (:state result)
        selection (:selection next-gesture)]
    (assoc result :state
           (cond-> (assoc state :cue-gesture next-gesture)
             (not= (get-in state [:cue-gesture :selection]) selection)
             (assoc :selected-cue (:cue-id selection) :selected-instance (:instance-id selection))
             (:target-consumed? result) (dissoc :target-once)))))

(defn- gesture-step [options state event model envelope]
  (gesture-result state
    (gesture/step (::gesture options) (:cue-gesture state) event
                  (assoc (select-keys state [:page-id :origin])
                         :pressed-buttons (:buttons state)
                         :target-selector (get-in state [:target-once :selector]))
                  model envelope)))

(defn- gesture-pad [options state event model envelope]
  (let [{:keys [gesture-key pressed? cell]} event]
    (cond
      (contains? (:picker-pads state) gesture-key)
      {:state (if pressed? state (targets/release-pad state gesture-key))}

      (and pressed? cell (:target-picker state)
           (not (contains? (get-in state [:cue-gesture :pads]) gesture-key)))
      {:state (targets/pad state gesture-key cell)}

      :else (gesture-step options state event model envelope))))

(defn- gesture-axis [options state key axis value model envelope]
  (gesture-step options state {:type :axis :gesture-key key :axis axis :value value} model envelope))

(defn- gesture-input [options state event model envelope]
  (case (:type event)
    :pad (gesture-pad options state (assoc event :cell (:control-id event)) model envelope)
    :poly-pressure (if (= :poly-aftertouch (:expression-mode options))
                     (gesture-axis options state (:gesture-key event) :pressure (:value event) model envelope)
                     {:state state})
    :mono-pressure (let [pads (keys (get-in state [:cue-gesture :pads]))]
                     (if (and (= :mono-aftertouch (:expression-mode options)) (= 1 (count pads))
                              (empty? (:picker-pads state)))
                       (gesture-axis options state (first pads) :pressure (:value event) model envelope)
                       {:state state}))
    :button (let [result (input options state event model envelope)
                  page (juxt :page-id :origin)]
              (if (= (page state) (page (:state result)))
                result
                (assoc result :state (:state (gesture-step options (:state result) {:type :context} model envelope)))))
    (input options state event model envelope)))

(defn- surface-state [state]
  (if-let [controls (:controls state)]
    (cond-> controls (and (not (:cue-gesture controls)) (get-in state [:mpe :selected-instance]))
      (assoc :selected-instance (get-in state [:mpe :selected-instance])))
    state))

(defn control-view
  "Pure grid and keyed parameter values for an external UI."
  [state model]
  (let [state (surface-state state)]
   (merge (display/view-options state model)
          {:page (:page-id state) :origin (:origin state)
   :selected-cue (:selected-cue state) :selected-instance (:selected-instance state)
   :target-picker (targets/view state)
   :touches (:touches state) :master (:master model) :blackout? (:blackout? model)
   :parameters (get-in model [:instances (:selected-instance state) :params] {})
   :cells (mapv (fn [[x y]] {:x x :y y :cue (some->> (cue-at state model [x y]) :id (views/cue-view model))})
                (for [y (range 8) x (range 8)] [x y]))})))

(defn- acknowledge [state command ack]
  (let [hold (when-let [gesture (:gesture-id command)]
               (bindings/acknowledge-hold (:holds state) gesture ack))
        key (:control/pad-key command) token (:control/selection-token command)
        accepted? (and (= :cue/launch (:op command)) (= :accepted (:status ack)) (:instance-id ack))]
    {:state (cond-> state
              hold (assoc :holds (:state hold))
              (and accepted? token (= token (:selection-token state))) (assoc :selected-instance (:instance-id ack))
              (and accepted? token (= token (get-in state [:pads key :token]))) (assoc-in [:pads key :instance-id] (:instance-id ack)))
     :commands (:commands hold)}))

(defn- modifier-ids [{:keys [temporary-encoder-modifier button-bindings]}]
  (case temporary-encoder-modifier
    nil #{}
    :shift (into #{} (keep (fn [[id action]] (when (= :shift action) id))) button-bindings)
    #{temporary-encoder-modifier}))

(defn- reset-encoder-model [options reset-model state]
  ;; A fresh show drops the gesture and its target. Held temporary touches need
  ;; their physical lift before a detent may edit the new selection.
  (let [physical (select-keys (encoder-gesture/reset-ownership state)
                              [:encoder-touch-modes :temporary-release-tails :dedicated-modifier-down?])
        held-modifiers (into #{} (filter (modifier-ids options)) (:buttons state))]
    (cond-> (merge (reset-model state) physical)
      (seq held-modifiers) (assoc :buttons held-modifiers))))

(defn- stale-encoder-input [options modifiers state {:keys [type control-id pressed?]} time-ms]
  (cond
    (and (= :encoder-touch type) (not pressed?)
         (= :temporary (get-in state [:encoder-touch-modes control-id])))
    (:state (release-encoder (encoder-gesture/observe-temporary-tails state time-ms) control-id time-ms))
    (and (= :encoder-touch type) pressed?
         (get-in options [:encoder-bindings control-id :param])
         (temporary-modifier-held? options state))
    (assoc-in state [:encoder-touch-modes control-id] :temporary)
    (and (= :button type) (contains? modifiers control-id))
    (set-held-button options state control-id pressed?)
    :else state))

(defn- user-profile
  "Construct a pure profile from a captured :layout. Explicit :user-mode? true
  confirms manual User Mode; :expression-mode is :poly-aftertouch or
  :mono-aftertouch. Optional :encoder-bindings maps captured IDs to {:param k,
  :step n} or {:target :master}; :button-bindings maps IDs to semantic actions.
  :pressure-param and :touch-strip-param opt into expression parameter control."
  [{:keys [layout user-mode? expression-mode page-id encoder-bindings button-bindings temporary-encoder-modifier]
    :or {page-id :main encoder-bindings {} button-bindings {}} :as options}]
  (valid! (true? user-mode?) "Manually enable Push 3 User Mode before connecting" {})
  (valid! (#{:poly-aftertouch :mono-aftertouch} expression-mode)
          "Select Poly Aftertouch or Mono Aftertouch; MPE routing is not implemented" {})
  (let [compiled (codec/compile-layout layout)]
    (valid! (or (some seq (vals layout)) (seq (:mpe-note-cells options))) "Capture at least one control before connecting" {})
    (valid! (and (map? encoder-bindings) (map? button-bindings)) "Control bindings must be maps" {})
    (doseq [[id binding] encoder-bindings]
      (valid! (and (contains? (:encoders layout) id) (map? binding)
                   (every? #{:param :target :step} (keys binding))
                   (or (and (keyword? (:param binding)) (nil? (:target binding)))
                       (and (= :master (:target binding)) (nil? (:param binding))))
                   (or (nil? (:step binding)) (and (params/finite-number? (:step binding)) (pos? (:step binding)))))
              "Encoder bindings need a captured ID, numeric parameter/master target and positive step" {:id id}))
    (doseq [[id action] button-bindings]
      (valid! (and (contains? (:buttons layout) id)
                   (or (display/action? action)
                       (#{:shift :blackout :transport :page-left :page-right :page-up :page-down :suspend :target-picker} action)
                       (and (::gesture options) (= action (get-in options [::gesture :gesture-modifier])))))
              "Button bindings need a captured ID and supported semantic action" {:id id}))
    (when (some? temporary-encoder-modifier)
      (let [ids (modifier-ids options)
            members (::mpe-members options)]
        (valid! (and (true? (:operator-gestures? options))
                     (keyword? temporary-encoder-modifier) (seq ids)
                     (every? #(and (contains? (:buttons layout) %)
                                   (not (contains? members (get-in layout [:buttons % :channel])))) ids))
                "Temporary encoder edits require operator gestures and a captured User Mode button"
                {:temporary-encoder-modifier temporary-encoder-modifier})))
    (doseq [key [:pressure-param :touch-strip-param] :when (contains? options key)]
      (valid! (keyword? (get options key)) "Expression targets must be parameter keywords" {:key key}))
    (when (contains? options :launch-mode)
      (valid! (#{:held :persistent :one-shot} (:launch-mode options)) "Invalid launch-mode override" {}))
    (let [reset-model (fn [state]
                        (cond-> (reset-interactions state)
                          (::gesture options) (assoc :cue-gesture (gesture/initial-state))))]
      (cond-> {:id :push-3 :capabilities capabilities
               :initial-state (reset-model {:page-id page-id :origin [0 0]})
               :decode (partial codec/decode compiled)
               :input (partial input options)
               :ack acknowledge
               :reset-model (partial reset-encoder-model options reset-model)
               :stop (fn [state _model envelope _disconnected?]
                       {:state (reset-model state)
                        :commands (bindings/release-holds (:holds state) envelope)})}
        (::gesture options)
        (assoc :capabilities (update capabilities :controls conj :cue-gestures)
               :input (partial gesture-input options)
               :ack (fn [state command ack]
                      (gesture-result state (gesture/acknowledge (:cue-gesture state) command ack)))
               :advance (fn [state model envelope]
                          (when-let [deadline (gesture/next-deadline-ms (:cue-gesture state))]
                            (when (<= deadline (:time-ms envelope))
                              (gesture-step options state {:type :tick} model envelope))))
               :unique-command-prefix? true
               :fence-captured-commands? true
               :stop (fn [state _model envelope _disconnected?]
                       (assoc (gesture/stop (:cue-gesture state) envelope) :state (reset-model state))))))))

(defn- mpe-profile [options]
  (valid! (seq (:mpe-note-cells options))
          "MPE needs explicit note-to-pad captures independent of rotating channels" {})
  (let [zone (mpe-codec/compile-zone (:zone options))
        controls (user-profile (assoc options :expression-mode :poly-aftertouch))
        notes (mpe/profile (assoc options :note-cells (:mpe-note-cells options)
                                 ::mpe/launch-grid (::grid options)
                                 :axes #{:strike :pressure :glide :slide}))
        initial {:controls (:initial-state controls) :mpe (:initial-state notes)}
        combine (fn [a b] {:state {:controls (:state a) :mpe (:state b)}
                          :commands (into (vec (:commands a)) (:commands b))})]
    {:id :push-3 :initial-state initial
     :capabilities (assoc capabilities :mpe :explicit-zone-and-note-captures
                          :available-axes (select-keys mpe-codec/axes [:strike :pressure :glide :slide])
                          :supported-expression-modes #{:mpe :poly-aftertouch :mono-aftertouch})
     :decode identity
     :input (fn [state bytes model envelope]
              (let [status (first bytes)
                    channel (when (and (integer? status) (<= 0x80 status 0xef)) (bit-and status 0x0f))
                    control-event ((:decode controls) bytes)
                    ;; Member channels belong exclusively to the expressive
                    ;; receiver. Do not collapse their rotating channel IDs.
                    member? (contains? (:member-channels zone) channel)
                    control-state (cond-> (:controls state)
                                    (get-in state [:mpe :selected-instance])
                                    (assoc :selected-instance (get-in state [:mpe :selected-instance])))]
                (cond
                  member? (let [note (second bytes) key [channel note]
                                cell (get (:mpe-note-cells options) note)
                                kind (bit-and status 0xf0)
                                press? (and (= 0x90 kind) (pos? (nth bytes 2 0)))
                                released? (or (= 0x80 kind) (and (= 0x90 kind) (not press?)))]
                            (cond
                              (contains? (:picker-pads control-state) key)
                              {:state (assoc state :controls (if released? (targets/release-pad control-state key) control-state))}
                              (and (:target-picker control-state) press? cell)
                              {:state (assoc state :controls (targets/pad control-state key cell))}
                              :else
                              (let [note-state (merge (:mpe state) (select-keys control-state [:page-id :origin]))
                                    result ((:input notes) note-state bytes model envelope)
                                    routed (targets/launch control-state (assoc result :state control-state))]
                                (assoc routed :state (assoc state :controls (:state routed) :mpe (:state result))))))
                  (and control-event (not (#{:pad :poly-pressure :mono-pressure} (:type control-event))))
                  (let [result ((:input controls) control-state control-event model envelope)]
                    (assoc result :state (assoc state :controls (:state result))))
                  :else {:state state})))
     :ack (fn [state command ack]
            (combine ((:ack controls) (:controls state) command ack)
                     ((:ack notes) (:mpe state) command ack)))
     :reset-model (fn [state] {:controls ((:reset-model controls) (:controls state))
                               :mpe ((:reset-model notes) (:mpe state))})
     :stop (fn [state model envelope disconnected?]
             (combine ((:stop controls) (:controls state) model envelope disconnected?)
                      ((:stop notes) (:mpe state) model envelope disconnected?)))}))

(defn- mpe-gesture-member [options zone state bytes model envelope]
  (let [{decoder :state :keys [events diagnostics]} (mpe-codec/advance zone (get-in state [:mpe :decoder]) bytes)
        state (-> state (assoc-in [:mpe :decoder] decoder)
                  (update-in [:mpe :diagnostics] #(vec (take-last 32 (into % diagnostics)))))]
    (reduce (fn [{:keys [state commands]} {:keys [type voice-id note axis value reason] :as event}]
              (let [controls (:controls state)
                    result (case type
                             (:note-on :note-off)
                             (gesture-pad options controls
                                          {:type :pad :gesture-key voice-id :cell (get (:mpe-note-cells options) note)
                                           :pressed? (= :note-on type) :axes (:axes event)
                                           :cancelled? (and (= :note-off type) (not= :released reason))}
                                          model envelope)
                             :axis (gesture-axis options controls voice-id axis value model envelope)
                             {:state controls})]
                {:state (assoc state :controls (:state result)) :commands (into commands (:commands result))}))
            {:state state :commands []} events)))

(defn- mpe-gesture-profile [options]
  (let [note-cells (:mpe-note-cells options)
        zone (mpe-codec/compile-zone (:zone options))
        surface (user-profile (assoc options :expression-mode :poly-aftertouch))
        initial-mpe {:decoder (mpe-codec/initial-state) :diagnostics []}
        lift (fn [state result]
               (when result (update result :state #(assoc state :controls %))))]
    (valid! (and (seq note-cells)
                 (every? (fn [[note cell]]
                           (and (integer? note) (<= 0 note 127) (vector? cell) (= 2 (count cell))
                                (every? #(and (integer? %) (<= 0 %)) cell))) note-cells))
            "MPE needs captured notes mapped to Push pad cells" {})
    (assoc surface
           :initial-state {:controls (:initial-state surface) :mpe initial-mpe}
           :capabilities (assoc (:capabilities surface) :mpe :explicit-zone-and-note-captures
                                :available-axes (select-keys mpe-codec/axes [:strike :pressure :glide :slide])
                                :supported-expression-modes #{:mpe :poly-aftertouch :mono-aftertouch})
           :decode identity
           :input (fn [state bytes model envelope]
                    (let [status (first bytes)
                          channel (when (and (integer? status) (<= 0x80 status 0xef)) (bit-and status 0x0f))]
                      (if (contains? (:member-channels zone) channel)
                        (mpe-gesture-member options zone state bytes model envelope)
                        (let [control ((:decode surface) bytes)]
                          (if (and control (not (#{:pad :poly-pressure :mono-pressure} (:type control))))
                            (lift state ((:input surface) (:controls state) control model envelope))
                            {:state state})))))
           :ack (fn [state command ack] (lift state ((:ack surface) (:controls state) command ack)))
           :advance (fn [state model envelope] (lift state ((:advance surface) (:controls state) model envelope)))
           :reset-model (fn [state] {:controls ((:reset-model surface) (:controls state)) :mpe initial-mpe})
           :stop (fn [state model envelope disconnected?]
                   (lift (assoc state :mpe initial-mpe)
                         ((:stop surface) (:controls state) model envelope disconnected?))))))

(defn- display-feedback [options state model _]
  (let [controls (surface-state state)
        index (push-view/cue-index model)
        instance (or (get-in model [:instances (:selected-instance controls)])
                     (when-not (get-in controls [:cue-gesture :selection]) (last (:active index))))
        touch (some (fn [id]
                      (when-let [k (get-in options [:encoder-bindings id :param])]
                        (when (get-in instance [:definition :params k])
                          {:instance-id (:id instance) :param k :component 0})))
                    (sort-by str (:touches controls)))
        selected (cond-> controls instance (assoc :selected-instance (:id instance) :selected-cue (:cue-id instance)))
        view (assoc (push-view/view selected model index {:status :ready :touched-parameter touch})
                    :fine? (boolean (shift-held? options controls)))
        selected (assoc selected :selected-instance (:id instance) :last-display view)
        next-state (if (:controls state)
                     (cond-> (assoc state :controls selected)
                       (not (:cue-gesture controls)) (assoc-in [:mpe :selected-instance] (:id instance)))
                     selected)]
    (cond-> {:state next-state}
      (not= view (:last-display controls)) (assoc :display view))))

(defn- with-encoder-gestures [{:keys [ack advance reconcile stop] :as profile}
                              {:keys [layout encoder-bindings expression-mode temporary-encoder-modifier]
                               :as options}]
  (let [mpe? (= :mpe expression-mode)
        member-channels (::mpe-members options)
        layout-codec (when mpe? (codec/compile-layout layout))
        modifiers (modifier-ids options)
        fixed-control (fn [event]
                        (let [control (if (and mpe? event) (codec/decode layout-codec event) event)]
                          (when-not (contains? member-channels (:channel control)) control)))
        controls (if mpe? :controls identity)
        lift (fn [state result]
               (if (and mpe? result)
                 (update result :state #(assoc state :controls %))
                 result))
        paired-encoders (filter (fn [[id binding]]
                                  (and (:param binding) (contains? (:encoder-touches layout) id)))
                                encoder-bindings)]
    (assoc profile
           :capabilities (update-in (:capabilities profile) [:controls] into
                                    (cond-> #{:operator-gestures}
                                      temporary-encoder-modifier (conj :temporary-encoder-edits)))
           :operator-gestures? true
           :gesture-end-limit (count paired-encoders)
           :ack (fn [state command receipt]
                  (if (#{:gesture/begin :gesture/sample :gesture/end :gesture/cancel} (:op command))
                    (lift state (encoder-gesture/acknowledge (controls state) command receipt))
                    (ack state command receipt)))
           :resume-gesture-begins (fn [state model ending-controls event]
                                    ;; In MPE mode session input is raw. Only fixed
                                    ;; control channels can lift an encoder touch.
                                    (let [control (fixed-control event)
                                          lifting (when (and (= :encoder-touch (:type control))
                                                             (not (:pressed? control)))
                                                    (:control-id control))]
                                      (lift state (encoder-gesture/resume-begins
                                                    (controls state) model ending-controls lifting))))
           :stale-input (fn [state event envelope]
                          (let [physical (stale-encoder-input options modifiers (controls state)
                                                              (fixed-control event) (:time-ms envelope))]
                            (:state (lift state {:state physical}))))
           :reconcile (fn [state model]
                        (let [{resolved :state commands :commands} (encoder-gesture/reconcile (controls state))
                              changed? (not (identical? (controls state) resolved))
                              state-result (lift state {:state resolved})]
                          (cond-> (or (when reconcile (reconcile (:state state-result) model))
                                      (when changed? state-result))
                            (seq commands) (update :commands #(into commands %))
                            changed? (assoc :refresh-model? true))))
           :advance (fn [state model envelope]
                      (let [result (when advance (advance state model envelope))
                            next-state (or (:state result) state)
                            surface (controls next-state)
                            observed (encoder-gesture/observe-temporary-tails surface (:time-ms envelope))
                            retries (encoder-gesture/retry-due {:state observed} (:time-ms envelope))]
                        (if (or (not (identical? surface observed)) (seq (:commands retries)))
                          (-> (merge result (lift next-state {:state (:state retries)}))
                              (update :commands (fnil into []) (:commands retries)))
                          result)))
           :stop (fn [state model envelope disconnected?]
                   (let [{resolved :state} (encoder-gesture/reconcile (controls state))
                         latest (:state (lift state {:state resolved}))]
                     (assoc (stop latest model envelope disconnected?)
                            :gesture-ends (encoder-gesture/detached-terminals resolved)))))))

(defn profile
  "Build Push 3 User Mode controls. :expression-mode :mpe additionally requires
  :zone and :mpe-note-cells {note [x y]} captured across rotating member channels.
  MPE exposes normalized Glide/Slide, not calibrated absolute pad coordinates.
  :cue-gestures? true opts into shared tap/hold policy. :hold-ms sets its deadline;
  bind a captured button to :cue-gesture or the configured :gesture-modifier.
  :operator-gestures? true groups touched scalar encoder edits for a trusted host.
  :temporary-encoder-modifier is :shift or a captured logical button ID. For
  :shift, map a captured button to the existing :shift action. Bind a touch
  note and turn CC to the same logical encoder ID to use temporary edits.
  :launch-grid optionally routes pad launches to a musical grid owned by the host."
  [options]
  (doseq [key [:cue-gestures? :operator-gestures?] :when (contains? options key)]
    (valid! (boolean? (get options key)) "Gesture opt-in must be boolean" {:option key}))
  (let [grid (launch/grid options)
        mpe? (= :mpe (:expression-mode options))
        modifier (:temporary-encoder-modifier options)
        options (cond-> (assoc options ::grid grid)
                  mpe? (assoc ::mpe-members (set (get-in options [:zone :member-channels])))
                  (and modifier (not= :shift modifier)) (assoc ::dedicated-modifier modifier)
                  (:cue-gestures? options)
                  (assoc ::gesture (gesture/configure
                                     (cond-> (assoc options :axes (if mpe? #{:strike :pressure :glide :slide}
                                                                         #{:strike :pressure}))
                                       mpe? (assoc :default-launch-mode :held)
                                       (:pressure-param options) (update :param-mappings
                                                                        #(merge {(:pressure-param options) :pressure} %))))))
        profile (cond
                  (and mpe? (::gesture options)) (mpe-gesture-profile options)
                  mpe? (mpe-profile options)
                  :else (user-profile options))]
    (cond-> (launch/with-grid profile grid (:launch-receipt options))
      (:display options) (assoc :feedback (partial display-feedback options))
      (:operator-gestures? options) (with-encoder-gestures options))))

(defn connect!
  "Explicitly open an injected MIDI transport. Manual session/suspend! and
  session/resume! provide handoff; User itself cannot be mapped in User Mode.
  A display must be an explicitly tagged Push 3 semantic transport. Cue and
  operator gestures use the supplied refresh schedule, or an owned 10 ms cadence."
  [options]
  (when-let [display (:display options)]
    (valid! (and (= :push-3 (:device display)) (= :view (:input display))
                 (every? #(fn? (get display %)) [:open! :render! :close!]))
            "Choose a tagged Push 3 display transport" {}))
  (session/open! (session/create (cond-> (assoc options :profile (profile options))
                                    (and (or (:cue-gestures? options) (:operator-gestures? options))
                                         (not (contains? options :schedule!)))
                                    (assoc :schedule! (transports/scheduler (get options :refresh-ms 10)))
                                    (and (:transport options) (not (:midi options))) (assoc :midi (:transport options))))))

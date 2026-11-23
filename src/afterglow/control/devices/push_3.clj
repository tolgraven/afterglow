(ns afterglow.control.devices.push-3
  "Push 3 User Mode controls over the shared semantic model. Addresses are
  captured explicitly; no Push 2 protocol, native display or LED output is used."
  (:require [afterglow.control.bindings :as bindings]
            [afterglow.control.codecs.push-3 :as codec]
            [afterglow.control.codecs.mpe :as mpe-codec]
            [afterglow.control.devices.mpe :as mpe]
            [afterglow.control.devices.session :as session]
            [afterglow.control.display :as display]
            [afterglow.control.devices.target-picker :as targets]
            [afterglow.control.params :as params]
            [afterglow.control.parameter-edit :as edit]
            [afterglow.control.views :as views]))

(def capabilities
  (assoc codec/capabilities :adapter :composable-session
         :controls #{:pad-cues :held-release :parameter-encoders :master-encoder
                     :parameter-pressure :parameter-touch-strip :page-scroll
                     :manual-handoff :reconnect :shift-fine}
         :feedback :data-view-only))

(defn- valid! [condition message data]
  (when-not condition (throw (ex-info message (assoc data :type ::invalid-options)))))

(defn- reset-interactions [state]
  (assoc (targets/clear-selection state) :pads {} :holds {} :buttons #{} :touches #{}
         :selected-instance nil :selected-cue nil :selection-token nil :shift-patch nil))

(defn- cue-at [state model [x y]]
  (let [[left bottom] (:origin state)
        id (get-in model [:pages (:page-id state) :cells [(+ left x) (+ bottom y)]])]
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
            (let [hold (bindings/begin-hold (:holds state) (:id cue) envelope)]
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

(defn- encoder [options state event model]
  (let [{:keys [target param step]} (get-in options [:encoder-bindings (:control-id event)])
        delta (:delta event) fine? (boolean (shift-held? options state))]
    (cond
      (zero? delta) {:state state}
      (= target :master)
      (let [increment (or step 0.01) value (bindings/clamp (+ (:master model) (* delta (if fine? (/ increment 10) increment))) [0 1])]
        {:state state :commands (if (= value (:master model)) [] [{:op :master/set :value value}])})
      (not fine?)
      (let [command (parameter-command model (:selected-instance state) param
                      (fn [value [low high] schema]
                        (+ value (* delta (or step (if (= :integer (:type schema)) 1 (/ (- high low) 100.0)))))))]
        {:state state :commands (if command [command] [])})
      :else
      (if-let [{:keys [instance schema value]} (numeric-parameter model (:selected-instance state) param)]
        (let [[cache bits] (when fine? (edit/patch-step (:shift-patch state) model instance param))
              schema (cond-> schema step (assoc :step step))
              next-value (edit/edit schema value delta {:fine? fine? :dmx-bits bits})]
          {:state (cond-> state cache (assoc :shift-patch cache))
           :commands (if (= value next-value) [] [{:op :param/set :instance-id (:id instance) :param param :value next-value}])})
        {:state state}))))

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

(defn- button [options state event model]
  (let [id (:control-id event) down? (:pressed? event)
        previously-down? (contains? (:buttons state) id)
        state (cond-> (update state :buttons (if down? conj disj) id)
                (and (not down?) (= :shift (get-in options [:button-bindings id]))) (dissoc :shift-patch))
        [x y] (:origin state)]
    (if (and down? (not previously-down?))
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
  (case (:type event)
     :pad (let [key (:gesture-key event)]
           (cond
             (contains? (:picker-pads state) key)
             {:state (if (:pressed? event) state (targets/release-pad state key))}
             (not (:pressed? event)) (release-pad state key envelope)
             (:target-picker state) {:state (targets/pad state key (:control-id event))}
             :else (targets/launch state (press-pad options state event model envelope))))
    :encoder (encoder options state event model)
    :encoder-touch {:state (update state :touches (if (:pressed? event) conj disj) (:control-id event))}
    (:poly-pressure :mono-pressure :touch-strip) (expression options state event model)
    :button (button options state event model)
    {:state state}))

(defn control-view
  "Pure labels/values for an external UI. This does not drive Push 3's display."
  [state model]
  (let [state (if (:controls state)
                (cond-> (:controls state)
                  (get-in state [:mpe :selected-instance])
                  (assoc :selected-instance (get-in state [:mpe :selected-instance]))) state)]
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

(defn- user-profile
  "Construct a pure profile from a captured :layout. Explicit :user-mode? true
  confirms manual User Mode; :expression-mode is :poly-aftertouch or
  :mono-aftertouch. Optional :encoder-bindings maps captured IDs to {:param k,
  :step n} or {:target :master}; :button-bindings maps IDs to semantic actions.
  :pressure-param and :touch-strip-param opt into expression parameter control."
  [{:keys [layout user-mode? expression-mode page-id encoder-bindings button-bindings]
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
                       (#{:shift :blackout :transport :page-left :page-right :page-up :page-down :suspend :target-picker} action)))
              "Button bindings need a captured ID and supported semantic action" {:id id}))
    (doseq [key [:pressure-param :touch-strip-param] :when (contains? options key)]
      (valid! (keyword? (get options key)) "Expression targets must be parameter keywords" {:key key}))
    (when (contains? options :launch-mode)
      (valid! (#{:held :persistent :one-shot} (:launch-mode options)) "Invalid launch-mode override" {}))
    {:id :push-3 :capabilities capabilities
     :initial-state (reset-interactions {:page-id page-id :origin [0 0]})
     :decode (partial codec/decode compiled)
     :input (partial input options)
     :ack acknowledge
     :reset-model reset-interactions
     :stop (fn [state _model _envelope _disconnected?]
             {:state (reset-interactions state)
              :commands (mapv (fn [id] {:op :instance/end :instance-id id})
                              (distinct (keep :instance-id (vals (get-in state [:holds :gestures])))))})}))

(defn- mpe-profile [options]
  (valid! (seq (:mpe-note-cells options))
          "MPE needs explicit note-to-pad captures independent of rotating channels" {})
  (let [zone (mpe-codec/compile-zone (:zone options))
        controls (user-profile (assoc options :expression-mode :poly-aftertouch))
        notes (mpe/profile (assoc options :note-cells (:mpe-note-cells options)
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

(defn profile
  "Build Push 3 User Mode controls. :expression-mode :mpe additionally requires
  :zone and :mpe-note-cells {note [x y]} captured across rotating member channels.
  MPE exposes normalized Glide/Slide, not calibrated absolute pad coordinates."
  [options]
  (if (= :mpe (:expression-mode options)) (mpe-profile options) (user-profile options)))

(defn connect!
  "Explicitly open an injected MIDI transport. Manual session/suspend! and
  session/resume! provide handoff; User itself cannot be mapped in User Mode.
  Native Push 3 display transport is unsupported and rejected."
  [options]
  (valid! (nil? (:display options)) "Push 3 native display protocol is not implemented" {})
  (session/open! (session/create (assoc options :profile (profile options)))))

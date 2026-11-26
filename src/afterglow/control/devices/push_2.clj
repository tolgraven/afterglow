(ns afterglow.control.devices.push-2
  "Composable Push 2 profile over the common command model. MIDI protocol comes
  from Afterglow's existing adapter; this module has no port or native UI access."
  (:require [afterglow.control.bindings :as bindings]
            [afterglow.control.parameter-edit :as parameter-edit]
            [afterglow.control.params :as params]
            [afterglow.control.codecs.midi :as midi]
            [afterglow.control.codecs.push-2 :as codec]
            [afterglow.control.pages :as pages]
            [afterglow.control.views :as views]
            [afterglow.control.display :as display]
            [afterglow.control.devices.encoder-gesture :as encoder-gesture]
            [afterglow.control.devices.active-cue-grid :as active-grid]
            [afterglow.control.devices.push-launch :as launch]
            [afterglow.control.devices.push-view :as push-view]
            [afterglow.control.devices.session :as session]
            [afterglow.control.devices.target-picker :as targets]))

(def capabilities
  (assoc codec/capabilities :adapter :composable-session
         :implemented #{:pad-cues :held-release :page-scroll :parameter-encoders
                        :parameter-banks :typed-parameters :effect-selection
                        :encoder-touch :touch-strip :color-grid :enum-grid :shift-fine
                        :velocity-parameters :pad-pressure :shift-held-override
                        :cue-parameter-presets
                        :touch-strip-feedback :master-touch :manual-tempo-encoder
                        :master-encoder :led-diff :palette-restore :display-view
                        :active-cue-grid :user-mode-handoff :reconnect}
         :hardware-verified? false))

(def ^:private accent-cc 57)

(defn- decode [device-id raw]
  (cond
    (map? raw) raw
    (= 0xf0 (first raw))
    (if-let [palette (codec/palette-reply device-id raw)]
      (assoc palette :type :palette)
      (when (= [0xf0 0 0x21 0x1d device-id 1 9] (vec (take 7 raw)))
        {:type :led-ack}))
    (and (integer? (first raw)) (<= 0x80 (first raw) 0xef)) (midi/decode raw)
    :else nil))

(defn- cue-at [state model note]
  (when-let [[x y] (codec/pad-coordinates note)]
    (let [[left bottom] (:origin state)
          cue-id (pages/cue-id-at model (:page-id state) [(+ left x) (+ bottom y)])]
      (get-in model [:registry :cues cue-id]))))

(defn- active-for-cue [model cue-id]
  (last (filter #(= cue-id (:cue-id %)) (views/active-instances model))))

(defn- select-instance [state instance]
  (if (= (:selected-instance state) (:id instance)) state
      (assoc state :selected-instance (:id instance) :selected-cue (:cue-id instance)
                   :touches {} :touch-order [])))

(defn- selected-state [state model]
  (if (get-in model [:instances (:selected-instance state)]) state
      (if-let [instance (last (views/active-instances model))]
        (select-instance state instance)
        (let [touches (into {} (filter (comp :target val)) (:touches state))]
          (assoc state :selected-instance nil :touches touches
                       :touch-order (filterv #(contains? touches %) (:touch-order state)))))))

(defn- parameter-at [state model encoder-index]
  (let [instance (get-in model [:instances (:selected-instance state)])
        id (nth (:ids (push-view/parameter-bank state instance)) encoder-index nil)]
    (when id
      {:instance-id (:id instance) :param id :encoder encoder-index
       :component (get-in state [:components [(:id instance) id]] 0)})))

(defn- live-parameter-touch? [state model touch]
  (and touch (= (:selected-instance state) (:instance-id touch))
       (get-in model [:instances (:instance-id touch) :definition :params (:param touch)])))

(defn- touched [state model]
  (let [touch (get (:touches state) (peek (:touch-order state)))]
    (when (live-parameter-touch? state model touch) touch)))

(defn- all-touched
  "Every held parameter touch on the selected live instance, by encoder slot."
  [state model]
  (->> (vals (:touches state))
       (filter #(live-parameter-touch? state model %))
       (sort-by :encoder)
       push-view/touched-parameters))

(defn- system-touch [state]
  (:target (get (:touches state) (peek (:touch-order state)))))

(defn- manual-clock? [model]
  (contains? #{nil :manual} (get-in model [:transport :source])))

(defn- edit-system [state model target input mode]
  (let [tempo? (= :tempo target)
        current (if tempo? (get-in model [:transport :bpm]) (:master model))
        bounds (if tempo? [20 200] [0 1])
        step (if tempo? (if (:shift? state) 1.0 0.1) (if (:shift? state) 0.001 0.01))
        next-value (bindings/clamp (if (= :absolute mode)
                                    (+ (first bounds) (* input (- (second bounds) (first bounds))))
                                    (+ current (* input step))) bounds)]
    {:state state
     :commands (if (or (= current next-value) (and tempo? (not (manual-clock? model)))) []
                   [(if tempo? {:op :transport/set :transport {:bpm next-value}}
                        {:op :master/set :value next-value})])}))

(defn- edit-parameter [parameter-editor state model selection value mode]
  (let [{:keys [instance-id param component]} selection
        instance (get-in model [:instances instance-id])
        schema (get-in instance [:definition :params param])
        current (get-in instance [:params param])]
    (if (and schema (or (= mode :absolute) (not (zero? value))))
      (let [[cache bits] (when (and (:shift? state) (= mode :relative))
                           (parameter-edit/patch-step (:shift-patch state) model instance param))
            options {:mode mode :component component :fine? (:shift? state) :dmx-bits bits}
            edit (when parameter-editor (parameter-editor model instance param value options))
            next-value (if edit (:value edit) (parameter-edit/edit schema current value options))]
        {:state (cond-> state cache (assoc :shift-patch cache)) :commands (if (= current next-value) []
                                    [{:op :param/set :instance-id instance-id :param param :value next-value}])})
      {:state state})))

(defn- encoder-control-id [note]
  (keyword "push-2" (str "encoder-" note)))

(defn- write-touched-parameter [state {:keys [instance-id param encoder]} value]
  (let [write {:state state :commands [{:op :param/set :instance-id instance-id :param param :value value}]}
        gesture (encoder-gesture/active state (encoder-control-id encoder))]
    (if (= :temporary (get-in state [:encoder-touch-modes encoder]))
      (if (and (:temporary? gesture) (= instance-id (:instance-id gesture)) (= param (:param gesture)))
        (encoder-gesture/edit state gesture (constantly write))
        {:state state})
      write)))

(defn- touch-encoder [state model note envelope operator-gestures? mode]
  (let [captured-mode (get-in state [:encoder-touch-modes note])
        temporary? (= :temporary (or captured-mode mode))
        state (cond-> state
                (and (< note 8) mode (nil? captured-mode)) (assoc-in [:encoder-touch-modes note] mode)
                (contains? (:temporary-release-tails state) note) (update :temporary-release-tails dissoc note))]
    (if-let [selection (case note
                         8 {:target :master :encoder note}
                         9 {:target :tempo :encoder note}
                         (parameter-at state model note))]
      (let [control-id (encoder-control-id note)
            gesture (get-in state [:encoder-gestures control-id])
            instance (get-in model [:instances (:instance-id selection)])
            schema (get-in instance [:definition :params (:param selection)])
            state (cond-> (-> state (assoc-in [:touches note] selection)
                              (update :touch-order #(conj (vec (remove #{note} %)) note)))
                    (and operator-gestures? (not (:released? gesture)))
                    (update :encoder-releases dissoc control-id))]
        (if (and operator-gestures? (= :running (:phase instance))
                 (if temporary? (params/valid-value? schema (get-in instance [:params (:param selection)]))
                     (#{:number :integer} (:type schema)))
                 ;; A duplicate touch must not give an unadmitted temporary touch a new target.
                 (not (and temporary? captured-mode)))
          (encoder-gesture/start state control-id selection envelope temporary?)
          {:state state}))
      {:state state})))

(defn- release-encoder [state note envelope]
  (let [mode (get-in state [:encoder-touch-modes note])
        touched? (contains? (:touches state) note)
        time-ms (:time-ms envelope)
        state (cond-> (-> state (update :touches dissoc note)
                          (update :touch-order #(vec (remove #{note} %))))
                mode (update :encoder-touch-modes dissoc note)
                (= :temporary mode) (encoder-gesture/start-temporary-tail note time-ms))]
    (encoder-gesture/release state (encoder-control-id note) time-ms touched?)))

(defn- retain-stale-encoder-input
  [modifier-cc modifier-key state {:keys [type note controller raw-value]} {:keys [time-ms] :as envelope}]
  (cond
    (and (:ready? state) (= :control-change type) (= modifier-cc controller))
    (assoc state modifier-key (pos? raw-value))

    (and (:ready? state) (= :note-on type) (<= 0 note 7) (get state modifier-key))
    ;; Keep the physical touch suppressed without selecting a new show target.
    (assoc-in state [:encoder-touch-modes note] :temporary)

    (and (= :note-off type) (= :temporary (get-in state [:encoder-touch-modes note])))
    (:state (release-encoder (encoder-gesture/observe-temporary-tails state time-ms) note envelope))

    :else state))

(defn- page-control [state model direction]
  (if (:shift? state)
    (let [instance (get-in model [:instances (:selected-instance state)])
          bank (push-view/parameter-bank state instance)
          next-bank (int (bindings/clamp (+ (:index bank) direction) [0 (dec (:count bank))]))]
      {:state (-> state (assoc-in [:parameter-banks (:id instance)] next-bank)
                  (assoc :touches {} :touch-order []))})
    (let [instances (views/active-instances model)
          index (or (first (keep-indexed #(when (= (:id %2) (:selected-instance state)) %1) instances))
                    (dec (count instances)))
          next-index (int (bindings/clamp (+ index direction) [0 (max 0 (dec (count instances)))]))]
      {:state (if-let [instance (nth instances next-index nil)] (select-instance state instance) state)})))

(defn- component-button [state model encoder-index]
  (if-let [{:keys [instance-id param component] :as selection} (parameter-at state model encoder-index)]
    (let [instance (get-in model [:instances instance-id])
          schema (get-in instance [:definition :params param])]
      (if (= :boolean (:type schema))
        (write-touched-parameter state selection (not (get-in instance [:params param])))
        (let [next-component (mod (inc component) (count (parameter-edit/components schema)))]
          {:state (-> state (assoc-in [:components [instance-id param]] next-component)
                      (update :touches (fn [touches]
                                         (into {} (map (fn [[note touch]]
                                                         [note (if (= (select-keys touch [:instance-id :param])
                                                                      (select-keys selection [:instance-id :param]))
                                                                 (assoc touch :component next-component) touch)])) touches))))})))
    {:state state}))

(defn- preset-command [state model]
  (let [instance (get-in model [:instances (:selected-instance state)])
        cue (get-in model [:registry :cues (:cue-id instance)])]
    {:state state
     :commands (if cue
                 [(cond-> {:op (if (:shift? state) :cue/clear-saved-params :cue/save-params)
                           :cue-id (:id cue) :expected-version (:version cue)}
                    (not (:shift? state)) (assoc :instance-id (:id instance)))] [])}))

(defn- picker-pad [state model note]
  (when-let [{:keys [instance-id param] :as selection} (touched state model)]
    (let [schema (get-in model [:instances instance-id :definition :params param])
          [x y] (codec/pad-coordinates note)
          value (case (:type schema)
                  :color (parameter-edit/color-grid-value schema x y)
                  :enum (nth (or (:values schema) (:options schema)) (+ x (* y 8)) ::missing)
                  ::missing)]
      (when (#{:color :enum} (:type schema))
        (if (= ::missing value) {:state state :commands []}
            (write-touched-parameter state selection value))))))

(defn- press-pad [grid state event model envelope]
  (if-let [cue (cue-at state model (:note event))]
    (let [mode (or (:launch-mode cue) (when (:held cue) :held) :persistent)
          mode (if (and (= :held mode) (:shift? state)) :persistent mode)
          effect (if-let [version (:effect-version cue)]
                   (or (get-in model [:registry :versions [:effects (:effect-id cue) version]])
                       (let [current (get-in model [:registry :effects (:effect-id cue)])]
                         (when (= version (:version current)) current)))
                   (get-in model [:registry :effects (:effect-id cue)]))
          launch-params (parameter-edit/velocity-values effect (:value event))
          note (:note event)
          launch-data {:mode mode :velocity (:value event) :params launch-params}
          active (active-for-cue model (:id cue))]
      (cond
        (or (get-in state [:pads note]) (and grid (contains? (:pressed-pads state) note))) {:state state}
        (= mode :held)
        (let [hold (bindings/begin-hold (:holds state) (:id cue) envelope grid)]
          {:state (cond-> (-> state (assoc :holds (:state hold) :selected-cue (:id cue))
                              (update :pressed-pads conj note)
                              (assoc-in [:pads note] (:gesture-id hold)))
                    grid (assoc :grid-selection (:command-id envelope))
                    grid (assoc-in [:grid-presses note] (:command-id envelope)))
           :commands (mapv #(assoc % :launch launch-data :pad-note note) (:commands hold))})
        (and (= mode :persistent) active (nil? (:target-once state)))
        {:state (-> state (assoc :selected-cue (:id cue) :selected-instance (:id active))
                    (dissoc :grid-selection)
                    (update :pressed-pads disj note) (update :pad-instances dissoc note))
         :commands [{:op :instance/end :instance-id (:id active)
                     :force? (= :releasing (:phase active))}]}
        :else
        {:state (cond-> (-> state (assoc :selected-cue (:id cue)) (update :pressed-pads conj note))
                  grid (assoc :grid-selection (:command-id envelope))
                  grid (assoc-in [:grid-presses note] (:command-id envelope)))
         :commands [{:op :cue/launch :cue-id (:id cue)
                     :pad-note note :launch launch-data}]}))
    {:state state}))

(defn- release-pad [state note envelope]
  (let [state (cond-> (-> state (update :pressed-pads disj note) (update :pad-instances dissoc note))
                (:grid-presses state) (update :grid-presses dissoc note))]
   (if-let [gesture (get-in state [:pads note])]
    (let [release (bindings/end-hold (:holds state) gesture envelope)]
      {:state (-> state (assoc :holds (:state release)) (update :pads dissoc note))
       :commands (:commands release)})
    {:state state})))

(defn- pressure-pad [state event model]
  (let [id (get-in state [:pad-instances (:note event)])
        instance (get-in model [:instances id])]
    {:state state
     :commands (if (and instance (contains? (:pressed-pads state) (:note event))
                         (= :running (:phase instance)))
                 (mapv (fn [[param value]] {:op :param/set :instance-id id :param param :value value})
                       (parameter-edit/velocity-values (:definition instance) (:value event))) [])}))

(defn- edit-encoder-gesture [parameter-editor state model {:keys [instance-id param component temporary?] :as gesture} value mode]
  (let [selection (cond-> gesture
                    temporary? (assoc :component (get-in state [:components [instance-id param]] component)))]
    (encoder-gesture/edit state gesture #(edit-parameter parameter-editor state model selection value mode))))

(defn- encoder [parameter-editor state event model envelope]
  (let [note (- (:controller event) 71)
        control-id (encoder-control-id note)
        gesture (encoder-gesture/active state control-id)
        delta (codec/signed-encoder (:raw-value event))]
    (cond
      gesture (edit-encoder-gesture parameter-editor state model gesture delta :relative)
      (= :temporary (get-in state [:encoder-touch-modes note])) {:state state}
      (contains? (:temporary-release-tails state) note) {:state state}
      (encoder-gesture/after-release? state control-id (:time-ms envelope)) {:state state}
      :else (edit-parameter parameter-editor state model (parameter-at state model note) delta :relative))))

(defn- edit-touch-strip [parameter-editor state model value]
  (if-let [target (system-touch state)]
    (edit-system state model target value :absolute)
    (let [{:keys [encoder] :as selection} (touched state model)
          gesture (when selection (encoder-gesture/active state (encoder-control-id encoder)))]
      (cond
        (and gesture (= (select-keys selection [:instance-id :param])
                        (select-keys gesture [:instance-id :param])))
        (edit-encoder-gesture parameter-editor state model gesture value :absolute)
        (= :temporary (get-in state [:encoder-touch-modes encoder])) {:state state}
        :else (edit-parameter parameter-editor state model selection value :absolute)))))

(defn- display-action [state model cc]
  (let [shift? (:shift? state)
        mode (display/mode state model)]
    (case cc
      51 (if shift? :display/page-colors :display/pages)
      31 (if shift? :display/rig :display/simulator)
      110 (if shift? :display/parameter-view :display/parameters)
      113 (if shift? :display/block-trace :display/audio)
      112 (when (#{:simulator :rig} mode) :display/camera)
      (62 63) (cond
                (= :rig mode) (if (= cc 62) :display/previous-fixture :display/next-fixture)
                (= :pages mode) (if (= cc 62) :display/previous-bank :display/next-bank)
                (and shift? (= :parameters mode)
                     (= :history (display/option state model :parameter-view :auto)))
                (if (= cc 62) :display/zoom-in :display/zoom-out))
      (when (and (= :pages mode) (<= 20 cc 27) (not (:record? state)))
        [:display/select-page (- cc 20)]))))

(defn- display-button [state model {:keys [type controller raw-value]}]
  (when (and (:ready? state) (= :control-change type) (not (:target-picker state)))
    (let [held? (contains? (:display-buttons state) controller)
          down? (pos? raw-value)
          action (display-action state model controller)]
      (cond
        held? {:state (if down? state (update state :display-buttons disj controller))}
        (and down? (display/action-supported? state action))
        {:state (-> state (update :display-buttons (fnil conj #{}) controller)
                    (display/apply-action model action))}))))

(defn- input [device-id grid operator-gestures? modifier-key parameter-editor state event model envelope]
  (let [state (selected-state state model)
        display-input (display-button state model event)]
   (cond
    display-input display-input
    (= :palette (:type event))
    (if (and (not (:ready? state)) (= (:index event) (:next-palette state)))
      (let [index (:index event)
            next-state (assoc-in state [:palettes index] (:rgbw event))]
        (if (= index 127)
          {:state (assoc next-state :ready? true :next-palette nil :fault nil)
           :midi [(codec/sysex device-id [0x0a 1]) (codec/sysex device-id [0x1e 1])]}
          {:state (assoc next-state :next-palette (inc index))
           :midi [(codec/palette-request device-id (inc index))]}))
      {:state state})
    (= :led-ack (:type event))
    {:state (assoc state :awaiting-led-ack? false :led-retries 0)}
    (and (= :control-change (:type event)) (= 59 (:controller event)) (pos? (:raw-value event)))
    {:state state :lifecycle :suspend}
    (not (:ready? state)) {:state state}
    (and (= :control-change (:type event)) (= 49 (:controller event)))
    {:state (cond-> (assoc state :shift? (pos? (:raw-value event)))
              (zero? (:raw-value event)) (dissoc :shift-patch))}
    (and (= :control-change (:type event)) (= 86 (:controller event)))
    {:state (assoc state :record? (pos? (:raw-value event)))}
    (and (= :note-on (:type event)) (<= 0 (:note event) 9))
    (let [mode (when modifier-key (if (get state modifier-key) :temporary :ordinary))]
      (touch-encoder state model (:note event) envelope operator-gestures? mode))
    (and (= :note-off (:type event)) (<= 0 (:note event) 9))
    (release-encoder state (:note event) envelope)
    (= :pitch-bend (:type event))
    (edit-touch-strip parameter-editor state model (:value event))
    (and (= :control-change (:type event)) (pos? (:raw-value event)) (#{62 63} (:controller event)))
    (page-control state model (if (= 62 (:controller event)) -1 1))
    (and (= :control-change (:type event)) (pos? (:raw-value event)) (<= 20 (:controller event) 27))
    (if (:record? state) (preset-command state model)
        (component-button state model (- (:controller event) 20)))
    (and (= :note-on (:type event)) (codec/pad-coordinates (:note event)))
    (or (picker-pad state model (:note event)) (press-pad grid state event model envelope))
    (= :note-off (:type event)) (release-pad state (:note event) envelope)
    (= :poly-pressure (:type event)) (pressure-pad state event model)
    (and (= :control-change (:type event)) (<= 71 (:controller event) 78))
    (encoder parameter-editor state event model envelope)
    (and (= :control-change (:type event)) (= 79 (:controller event)))
    (edit-system state model :master (codec/signed-encoder (:raw-value event)) :relative)
    (and (= :control-change (:type event)) (= 15 (:controller event)))
    (edit-system state model :tempo (codec/signed-encoder (:raw-value event)) :relative)
    (and (= :control-change (:type event)) (pos? (:raw-value event)) (#{44 45 46 47} (:controller event)))
    (let [[x y] (:origin state)
          next-origin (case (:controller event) 44 [(max 0 (- x 8)) y]
                            45 [(+ x 8) y] 46 [x (+ y 8)] 47 [x (max 0 (- y 8))])]
      {:state (assoc state :origin next-origin :last-leds {})})
    (and (= :control-change (:type event)) (= 85 (:controller event)) (pos? (:raw-value event)))
    {:state state :commands [{:op :blackout/set :value (not (:blackout? model))}]}
    :else {:state state})))

(defn- rgb [cue]
  (let [candidate (:color cue)
        color (if (and (vector? candidate) (= 3 (count candidate))
                       (every? #(and (number? %) (Double/isFinite (double %))) candidate))
                candidate [0.35 0.35 0.35])
        brightness (cond (:releasing? cue) 0.45 (:active? cue) 1.0 :else 0.25)]
    (mapv #(int (Math/round (* 255.0 brightness (bindings/clamp % [0 1])))) color)))

(defn- indexed-display [state model index]
  (let [state (selected-state state model)
        target (system-touch state)]
    (push-view/view state model index
                    {:status (or (:fault state) (if (:ready? state) :ready :loading-palettes))
                     :touched-parameter (touched state model)
                     :touched-parameters (all-touched state model)
                     :touched-control (when target
                                        {:target target :editable? (or (= :master target) (manual-clock? model))})})))

(defn display-view
  "Device-independent labels/values. A display transport draws this map."
  [state model]
  (let [grid (active-grid/project (:active-grid state) model)]
    (cond-> (indexed-display state model (push-view/cue-index model))
      grid (assoc :active-cue-grid (:view grid)))))

(defn- strip-feedback [state model]
  (if-let [target (system-touch state)]
    (if (and (= :tempo target) (not (manual-clock? model))) {:mode :off}
      {:mode :level :value (long (Math/round (* 16383.0
                       (if (= :master target) (:master model)
                         (bindings/clamp (/ (- (get-in model [:transport :bpm]) 20) 180.0) [0 1])))))})
    (if-let [{:keys [instance-id param component]} (touched state model)]
      (let [schema (get-in model [:instances instance-id :definition :params param])
            value (get-in model [:instances instance-id :params param])
            mode (cond (or (= :enum (:type schema)) (and (= :color (:type schema)) (zero? component))) :point
                       (or (= :boolean (:type schema)) (:centered schema)) :centered
                       :else :level)]
        {:mode mode :value (long (Math/round (* 16383.0 (parameter-edit/position schema value {:component component}))))})
      {:mode :off})))

(defn- next-led-batch [desired {:keys [last-leds led-cursor] :or {led-cursor 0}} limit]
  ;; Keep the ACK budget fair even when the first few pads change every frame.
  (into [] (comp (map (fn [offset]
                        (let [index (mod (+ led-cursor offset) 64)
                              xy [(quot index 8) (mod index 8)]]
                          [xy (get desired xy)])))
                 (remove (fn [[xy color]] (= color (get last-leds xy))))
                 (take limit))
        (range 64)))

(def ^:private active-grid-buttons {48 :select 88 :reorder})

(defn- reset-active-grid [state]
  (if-let [{:keys [mode pressed clearing?]} (:active-grid state)]
    (assoc state :active-grid (cond-> (assoc active-grid/initial-state :pressed pressed)
                               (or mode clearing?) (assoc :clearing? true)))
    state))

(defn- mode-lights [[mode source?]]
  (mapv (fn [[cc button-mode]]
          [0xb0 cc (cond (not= mode button-mode) 0
                         (and (= :reorder mode) (not source?)) 64
                         :else 127)])
        active-grid-buttons))

(defn- set-active-grid-mode [state mode]
  (let [current (get-in state [:active-grid :mode])]
    (cond-> (update state :active-grid active-grid/set-mode mode)
      (and current (nil? mode)) (assoc-in [:active-grid :clearing?] true)
      mode (dissoc :target-picker))))

(defn- active-grid-input [state event model]
  (when-let [{:keys [mode pressed buttons clearing?] :as grid} (:active-grid state)]
    (when (:ready? state)
      (let [{:keys [type note controller raw-value]} event
            control? (= :control-change type)
            coordinates (when (= :note-on type) (codec/pad-coordinates note))]
        (cond
          (and control? (active-grid-buttons controller))
          (let [down? (pos? raw-value)
                mode-button (active-grid-buttons controller)
                state (update-in state [:active-grid :buttons] (fnil (if down? conj disj) #{}) controller)]
            {:state (if (and down? (not (contains? buttons controller)))
                      (set-active-grid-mode state (when (not= mode mode-button) mode-button))
                      state)})

          (and mode control? (#{62 63} controller))
          {:state (if (pos? raw-value)
                    (update state :active-grid active-grid/step-page model (if (= controller 62) -1 1))
                    state)}

          (and (= :note-off type) (contains? pressed note))
          {:state (assoc state :active-grid (:state (active-grid/release grid note)))}

          (and coordinates (not (contains? (:pressed-pads state) note)))
          (if clearing?
            {:state (update-in state [:active-grid :pressed] conj note)}
            (let [{:keys [handled? selection commands] next-grid :state}
                  (active-grid/press grid model note coordinates)]
              (when handled?
                {:state (cond-> (assoc state :active-grid next-grid)
                          selection (-> (select-instance (get-in model [:instances (:instance-id selection)]))
                                        (dissoc :grid-selection)))
                 :commands commands}))))))))

(defn- pad-overlay-input [overlay state event model]
  (when (and overlay (:ready? state))
    (let [{:keys [type note controller]} event
          xy (when note (codec/pad-coordinates note))
          owned? (contains? (:pad-overlay-pressed state) note)
          other-owned? (or (contains? (:pressed-pads state) note) (contains? (:picker-pads state) note)
                           (contains? (get-in state [:active-grid :pressed]) note))
          other-mode? (or (:target-picker state) (get-in state [:active-grid :mode])
                          (get-in state [:active-grid :clearing?]))
          overlay-state (:pad-overlay state)
          clearing? (:pad-overlay-clearing? state)]
      (cond
        owned? {:state (cond-> state (= :note-off type) (update :pad-overlay-pressed disj note))}
        (or other-owned? other-mode?) nil
        (and (or overlay-state clearing?) (= :control-change type)
             (or (active-grid-buttons controller) (= 111 controller))) {:state state}
        :else
        (let [press? (and xy (= :note-on type) (or overlay-state clearing?))
              change (when-not (and press? (nil? (:pad-overlay-presented state)))
                       ((:input overlay) overlay-state event model
                        {:position xy :presented (:pad-overlay-presented state)
                         :selected-instance (:selected-instance state) :record? (:record? state)}))]
          (when (or press? change)
            (let [next-overlay (:state change overlay-state)]
              {:state (cond-> (assoc state :pad-overlay next-overlay)
                        press? (update :pad-overlay-pressed (fnil conj #{}) note)
                        (not= overlay-state next-overlay) (dissoc :pad-overlay-presented)
                        (and overlay-state (nil? next-overlay)) (assoc :pad-overlay-clearing? true))
               :commands (:commands change)})))))))

(defn- encoder-overlay-input
  "Offer a decoded event to the host's encoder overlay. A nil result leaves the
  event to Push; otherwise the result's :state and :commands are the outcome."
  [overlay state event model]
  (when (and overlay (:ready? state))
    (when-let [change ((:input overlay) (:encoder-overlay state) event model
                       {:shift? (boolean (:shift? state))
                        :touched (into (sorted-set) (filter #(<= 0 % 7))
                                       (concat (keys (:touches state)) (keys (:encoder-touch-modes state))))})]
      {:state (assoc state :encoder-overlay (:state change (:encoder-overlay state)))
       :commands (vec (:commands change))})))

(defn- feedback [device-id timeout-ms batch-size pad-overlay encoder-overlay state model envelope]
  (let [time (:time-ms envelope)
        state (encoder-gesture/observe-temporary-tails (selected-state state model) time)
        alive (set (keys (:instances model)))
        state (-> state (update :parameter-banks #(select-keys % alive))
                  (update :components #(into {} (filter (fn [[[id _] _]] (alive id))) %)))
        touch (touched state model)
        schema (get-in model [:instances (:instance-id touch) :definition :params (:param touch)])
        waiting? (:awaiting-led-ack? state)
        timed-out? (and waiting? (>= (- time (:last-led-at-ms state time)) timeout-ms))
        state (cond
                (and (not (:ready? state)) (>= (- time (:palette-start-ms state time)) timeout-ms))
                (assoc state :fault :palette-timeout)
                (and timed-out? (>= (:led-retries state 0) 2))
                (assoc state :fault :led-timeout)
                timed-out? (-> state (assoc :awaiting-led-ack? false :last-leds {}) (update :led-retries (fnil inc 0)))
                :else state)
        index (push-view/cue-index model)
        grid (active-grid/project (:active-grid state) model)
        overlay (when-let [overlay-state (:pad-overlay state)]
                  ((:project pad-overlay) overlay-state model (:pad-overlay-projection state)))
        state (cond-> state
                overlay (assoc :pad-overlay-projection overlay)
                (and (:pad-overlay state) (nil? overlay))
                (-> (dissoc :pad-overlay :pad-overlay-projection :pad-overlay-presented)
                    (assoc :pad-overlay-clearing? true)))
        display (cond-> (indexed-display state model index)
                  encoder-overlay (merge ((:project encoder-overlay) (:encoder-overlay state) model))
                  grid (assoc :active-cue-grid (:view grid))
                  overlay (assoc :pad-overlay (:display overlay (:view overlay)))
                  (get-in overlay [:display :title]) (assoc :title (get-in overlay [:display :title])))
        display-changed? (not= display (:last-display state))
        state (assoc state :last-display display)
        strip (strip-feedback state model)
        strip-messages (when (and (:ready? state) (nil? (:fault state)))
                         (codec/touch-strip-messages device-id (:last-touch-strip state) strip))
        state (if (some? strip-messages) (assoc state :last-touch-strip strip) state)
        desired (cond
                  overlay (into {} (for [y (range 8) x (range 8)]
                                     [[x y] (get (:colors overlay) [x y] [0 0 0])]))
                  grid (into {} (for [y (range 8) x (range 8)]
                             [[x y] (if-let [cell (get-in grid [:view :cells (+ x (* 8 y))])]
                                      (rgb (assoc cell :active? true))
                                      [0 0 0])]))
                  :else (into {} (for [y (range 8) x (range 8)]
                             (let [cue (cue-at state model (codec/pad-note x y))]
                               [[x y] (if-let [{:keys [offset rows]} (:target-picker state)]
                                        (if (zero? y)
                                          (case (:kind (get rows (+ offset x)))
                                            :group [80 180 130] :volume [230 150 65] :fixture [55 130 195] :default [100 100 100] [0 0 0])
                                          [0 0 0])
                                        (case (:type schema)
                                          :color (mapv #(int (Math/round (* 255.0 %))) (parameter-edit/color-grid-value schema x y))
                                          :enum (let [value (nth (or (:values schema) (:options schema)) (+ x (* y 8)) ::missing)
                                                      selected (get-in model [:instances (:instance-id touch) :params (:param touch)])]
                                                  (cond (= ::missing value) [0 0 0] (= selected value) [255 255 255] :else [30 70 120]))
                                          (if cue (rgb (views/pad-view model (:id cue) (:by-cue index))) [0 0 0])))]))))
        settled? (and (:ready? state) (nil? (:fault state)) (not (:awaiting-led-ack? state))
                      (= desired (:last-leds state)))
        state (cond-> state
                (and overlay settled?) (assoc :pad-overlay-presented (:view overlay))
                (and overlay (not settled?)) (dissoc :pad-overlay-presented)
                (and (nil? overlay) settled?)
                (dissoc :pad-overlay-clearing? :pad-overlay-projection :pad-overlay-presented)
                (and grid settled?) (update :active-grid #(-> (active-grid/capture % grid) (dissoc :clearing?)))
                (and (nil? grid) settled? (get-in state [:active-grid :clearing?]))
                (update :active-grid dissoc :clearing?))
        changes (when (and (:ready? state) (nil? (:fault state)) (not (:awaiting-led-ack? state)))
                  (next-led-batch desired state batch-size))
        [last-x last-y] (first (peek changes))
        indicator [(get-in grid [:view :mode]) (boolean (get-in grid [:view :source-instance-id]))]
        lights (when (and (:ready? state) (nil? (:fault state)) (:active-grid state)
                          (not= indicator (:last-grid-indicator state)))
                 (mode-lights indicator))
        messages (into (into (vec strip-messages) lights) (mapcat (fn [[[x y] color]]
                               (codec/pad-led-messages device-id x y color
                                 (last (get-in state [:palettes (codec/pad-note x y)])))) changes))
        keepalive? (and (:ready? state) (nil? (:fault state)) (not (:awaiting-led-ack? state))
                        (empty? changes) (>= (- time (:last-led-at-ms state time)) (/ timeout-ms 2)))
        query? (or (seq changes) keepalive?)]
    (cond-> {:state (cond-> state
                     lights (assoc :last-grid-indicator indicator)
                     (seq changes) (assoc :last-leds (into (:last-leds state) changes)
                                          :led-cursor (mod (inc (+ (* 8 last-x) last-y)) 64))
                     query? (assoc :awaiting-led-ack? true :last-led-at-ms time))
             :midi (cond-> messages query? (conj (codec/sysex device-id [0x09])))}
      display-changed? (assoc :display display)
      (:fault state) (assoc :lifecycle :disconnect))))

(defn- stop [device-id state _model envelope disconnected?]
  {:state (cond-> (assoc (dissoc (targets/clear-selection state) :grid-selection :grid-presses
                                :encoder-gestures :encoder-releases :encoder-touch-modes
                                :temporary-release-tails :temporary-release-time-ms
                                :pad-overlay :pad-overlay-pressed :pad-overlay-clearing?
                                :pad-overlay-projection :pad-overlay-presented)
                 :pads {} :holds {} :ready? false :last-leds {} :last-display nil
                 :last-touch-strip nil :display-buttons #{}
                 :touches {} :touch-order [] :shift? false :shift-patch nil :record? false
                 :temporary-encoder-modifier-down? false :pressed-pads #{} :pad-instances {})
            (:active-grid state) (assoc :active-grid active-grid/initial-state :last-grid-indicator nil))
   :gesture-ends (encoder-gesture/detached-terminals state)
   :commands (bindings/release-holds (:holds state) envelope)
   :midi (if (or disconnected? (not (:ready? state))) []
             (into (into (cond-> [(codec/touch-strip-mode device-id :default)]
                           (:active-grid state) (into (mode-lights nil)))
                         (for [note (range 36 100)] [0x80 note 0]))
                   (map (fn [[index rgbw]] (codec/palette-write device-id index rgbw)))
                   (sort-by key (:palettes state))))})

(defn- with-encoder-gestures [profile]
  (let [{:keys [feedback reconcile stop]} profile]
    (assoc profile
           :operator-gestures? true
           :resume-gesture-begins (fn [state model ending-controls event]
                                    (let [lifting (when (= :note-off (:type event)) (encoder-control-id (:note event)))]
                                      (encoder-gesture/resume-begins state model ending-controls lifting)))
           :feedback (fn [state model envelope]
                       (let [result (feedback state model envelope)]
                         (if (and (get-in result [:state :ready?]) (nil? (:lifecycle result)))
                           (encoder-gesture/retry-due result (:time-ms envelope))
                           result)))
           :stop (fn [state model envelope disconnected?]
                   ;; Settle receipts for cleanup without enacting a waiting touch.
                   (stop (:state (encoder-gesture/reconcile state)) model envelope disconnected?))
           :reconcile (fn [state model]
                        (let [{resolved :state commands :commands} (encoder-gesture/reconcile state)
                              resolved? (not (identical? resolved state))]
                          (cond-> (or (when reconcile (reconcile resolved model))
                                      (when resolved? {:state resolved}))
                            (seq commands) (update :commands #(into commands %))
                            resolved? (assoc :refresh-model? true)))))))

(defn- with-encoder-overlay-reset [profile reset]
  (let [{:keys [stop reset-model]} profile
        reset-overlay #(cond-> % (contains? % :encoder-overlay) (update :encoder-overlay reset))]
    (assoc profile
           :stop (fn [state model envelope disconnected?]
                   (update (stop state model envelope disconnected?) :state reset-overlay))
           :reset-model (fn [state] (reset-overlay (reset-model state))))))

(defn profile
  "Build a Push 2 profile with an explicitly known MIDI device-id and page-id.
  Sequential palette acquisition precedes writes; LEDs use acknowledged batches.
  Missing responses are reported on refresh!, never guessed. :launch-grid
  optionally routes pad launches to a musical grid owned by the host. Set
  :operator-gestures? true with a trusted host dispatcher to group touched scalar
  encoders. Hold Accent while touching an authored parameter encoder to restore
  its value on lift. :temporary-encoder-modifier can override Accent with a MIDI
  button CC. Legacy :shift and CC 49 settings select Accent and keep Shift fine.
  The host must settle pending ends and cancels after prior samples. Detents
  without touch use ordinary control after a short release tail.
  :active-cue-grid? enables Select and Duplicate to open separate active
  instance modes, with Page Left/Right for pagination.
  Optional :pad-overlay is a host projection and input pair. :project takes
  local overlay state, the model and its prior projection; return :colors by
  pad coordinate and a :view, or nil to dismiss. :input takes local overlay
  state, decoded event, committed model and context with :selected-instance,
  :record?, :position and the LED-acknowledged :presented view. Return a new
  overlay :state and optional :commands, or nil to leave the event to Push.
  Optional :parameter-editor takes model, instance, parameter, input and edit
  options. Return {:value v} to use a host-specific exact representation through
  the normal parameter and gesture dispatch, or nil to use Afterglow typed editing.
  Optional :encoder-overlay {:input f :project f :reset f} lets a host take
  encoders, touches and buttons. :input takes the overlay state, a decoded event,
  the committed model and {:shift? :touched}, where :touched is the set of track
  encoders (0-7) Push holds a touch or touch mode for. Return {:state s :commands
  [...]} to consume the event, or nil to leave it to Push. :project takes the
  overlay state and model and returns a map merged into the display view.
  Optional :reset takes the overlay state when Push resets or stops."
  [{:keys [device-id page-id timeout-ms led-batch-size target-search display launch-receipt
           operator-gestures? temporary-encoder-modifier active-cue-grid? pad-overlay parameter-editor
           encoder-overlay]
    :or {device-id 0 page-id :main timeout-ms 1500 led-batch-size 8} :as options}]
  (codec/palette-request device-id 0)
  (when (and pad-overlay (not (every? ifn? ((juxt :input :project) pad-overlay))))
    (throw (ex-info "Pad overlay requires input and projection functions" {})))
  (when (and encoder-overlay (not (and (every? ifn? ((juxt :input :project) encoder-overlay))
                                       (or (nil? (:reset encoder-overlay)) (ifn? (:reset encoder-overlay))))))
    (throw (ex-info "Encoder overlay requires input and projection functions" {})))
  (when-not (and (number? timeout-ms) (pos? timeout-ms)
                 (integer? led-batch-size) (<= 1 led-batch-size 16))
    (throw (ex-info "Invalid Push 2 timeout/batch size" {})))
  (when (and (some? temporary-encoder-modifier)
             (not (and (true? operator-gestures?)
                       (or (#{:accent :shift} temporary-encoder-modifier)
                           (and (integer? temporary-encoder-modifier) (<= 0 temporary-encoder-modifier 127))))))
    (throw (ex-info "Temporary encoder edits require operator gestures and an Accent or MIDI button CC setting"
                    {:temporary-encoder-modifier temporary-encoder-modifier})))
  (let [modifier-cc (when (true? operator-gestures?)
                      (if (contains? #{nil :accent :shift 49} temporary-encoder-modifier)
                        accent-cc temporary-encoder-modifier))
        modifier-key (when (some? modifier-cc) :temporary-encoder-modifier-down?)
        grid (launch/grid options)
        {:keys [modes actions] :as display-capabilities} (:display-capabilities display)
        _ (when-not (and (or (nil? modes) (and (set? modes) (seq modes) (every? display/modes modes)))
                         (or (nil? actions) (set? actions)))
            (throw (ex-info "Invalid Push 2 display capabilities" {:display-capabilities display-capabilities})))
        initial (cond-> {:page-id page-id :origin [0 0] :palettes {} :next-palette 0
                         :ready? false :pads {} :holds {} :last-leds {} :led-retries 0 :display-buttons #{}
                         :parameter-banks {} :components {} :touches {} :touch-order [] :shift? false :shift-patch nil :record? false
                         :pressed-pads #{} :pad-instances {}}
                  display-capabilities (assoc :display-capabilities display-capabilities)
                  (true? active-cue-grid?) (assoc :active-grid active-grid/initial-state))]
    (cond->
     (launch/with-grid
     {:id :push-2 :capabilities capabilities :initial-state initial
     :decode (partial decode device-id)
     :start (fn [state _model envelope]
              {:state (assoc state :palette-start-ms (:time-ms envelope))
               :midi [(codec/palette-request device-id 0)]})
     :input (fn [state event model envelope]
              (let [state (encoder-gesture/observe-temporary-tails state (:time-ms envelope))
                    control (when (and (:ready? state) (= :control-change (:type event))) (:controller event))
                    down? (and control (pos? (:raw-value event)))
                    cc (when down? control)
                    modifier-input? (and control (= modifier-cc control))
                    encoder-input (when-not modifier-input?
                                    (encoder-overlay-input encoder-overlay state event model))
                    overlay-input (when (and pad-overlay (not modifier-input?) (not encoder-input))
                                    (pad-overlay-input pad-overlay (selected-state state model) event model))
                    [x y] (when (= :note-on (:type event)) (codec/pad-coordinates (:note event)))]
                (cond
                  modifier-input? {:state (assoc state modifier-key down?)}
                  encoder-input encoder-input
                  overlay-input overlay-input
                  (and target-search (= 111 cc))
                  {:state (targets/toggle (cond-> state (:active-grid state) (set-active-grid-mode nil))
                                          target-search model)}
                  (and (:target-picker state) (#{62 63} cc)) {:state (targets/page state (if (= cc 62) -1 1))}
                  (and (:target-picker state) cc (<= 20 cc 27)) {:state (targets/choose state (- cc 20))}
                  (contains? (:picker-pads state) (:note event))
                  {:state (if (= :note-off (:type event)) (targets/release-pad state (:note event)) state)}
                  :else (or (active-grid-input state event model)
                            (if (and (:target-picker state) x)
                              {:state (targets/pad state (:note event) [x y])}
                              (targets/launch state (input device-id grid (true? operator-gestures?)
                                                           modifier-key parameter-editor state event model envelope)))))))
     :feedback (partial feedback device-id timeout-ms led-batch-size pad-overlay encoder-overlay)
     :stop (partial stop device-id)
     :resume-event? #(and (= :control-change (:type %)) (= 59 (:controller %)) (pos? (:raw-value %)))
     :reset-model (fn [state]
                    (reset-active-grid
                      (cond-> (assoc (dissoc (encoder-gesture/reset-ownership (targets/clear-selection state))
                                             :grid-selection :grid-presses :pad-overlay :pad-overlay-pressed
                                             :pad-overlay-clearing? :pad-overlay-projection :pad-overlay-presented)
                                     :display-buttons #{} :pads {} :holds {} :selected-instance nil :selected-cue nil :last-leds {} :last-touch-strip nil
                                     :parameter-banks {} :components {} :touches {} :touch-order [] :shift? false :shift-patch nil :record? false
                                     :temporary-encoder-modifier-down? false :pressed-pads #{} :pad-instances {})
                        modifier-key (assoc modifier-key (boolean (get state modifier-key))))))
     :ack (fn [state command ack]
            (if (#{:gesture/begin :gesture/sample :gesture/end :gesture/cancel} (:op command))
              (encoder-gesture/acknowledge state command ack)
              (let [hold (when-let [gesture (:gesture-id command)]
                           (bindings/acknowledge-hold (:holds state) gesture ack))
                    accepted? (and (= :cue/launch (:op command)) (= :accepted (:status ack)))
                    note (:pad-note command)
                    token (:command-id command)
                    gridded? (contains? command :grid)
                    selected? (and accepted? (or (not gridded?) (= token (:grid-selection state))))]
                {:state (cond-> state
                          hold (assoc :holds (:state hold))
                          selected? (assoc :selected-instance (:instance-id ack))
                          (and selected? gridded?) (assoc :selected-cue (:cue-id command))
                          (and accepted? (contains? (:pressed-pads state) note)
                               (or (not gridded?) (= token (get-in state [:grid-presses note]))))
                          (assoc-in [:pad-instances note] (:instance-id ack)))
                 :commands (:commands hold)})))}
      grid launch-receipt)
      modifier-key (assoc :stale-input (partial retain-stale-encoder-input modifier-cc modifier-key))
      (:reset encoder-overlay) (with-encoder-overlay-reset (:reset encoder-overlay))
      (true? operator-gestures?) with-encoder-gestures)))

(defn connect!
  "REPL facade: options are session options plus :device-id/:page-id. Supply MIDI
  and optional display transports; no device is guessed or automatically bound.
  A display can declare :display-capabilities with a nonempty set of :modes and
  a set of supported display :actions. Omitted keys allow all modes or actions."
  [options]
  (when-let [device (get-in options [:display :device])]
    (when-not (= :push-2 device)
      (throw (ex-info "Select a Push 2 display transport" {:device device}))))
  (session/open! (session/create (assoc options :profile (profile options)))))

(ns afterglow.control.devices.push-2
  "Composable Push 2 profile over the common command model. MIDI protocol comes
  from Afterglow's existing adapter; this module has no port or native UI access."
  (:require [afterglow.control.bindings :as bindings]
            [afterglow.control.parameter-edit :as parameter-edit]
            [afterglow.control.codecs.midi :as midi]
            [afterglow.control.codecs.push-2 :as codec]
            [afterglow.control.views :as views]
            [afterglow.control.devices.session :as session]))

(def capabilities
  (assoc codec/capabilities :adapter :composable-session
         :implemented #{:pad-cues :held-release :page-scroll :parameter-encoders
                        :parameter-banks :typed-parameters :effect-selection
                        :encoder-touch :touch-strip :color-grid :enum-grid :shift-fine
                        :velocity-parameters :pad-pressure :shift-held-override
                        :master-encoder :led-diff :palette-restore :display-view
                        :user-mode-handoff :reconnect}
         :hardware-verified? false))

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
          cue-id (get-in model [:pages (:page-id state) :cells [(+ left x) (+ bottom y)]])]
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
        (assoc state :selected-instance nil :touches {} :touch-order []))))

(defn- parameter-bank [state instance]
  (let [ids (parameter-edit/ordered-parameters (:definition instance))
        banks (max 1 (long (Math/ceil (/ (count ids) 8.0))))
        index (int (bindings/clamp (get-in state [:parameter-banks (:id instance)] 0) [0 (dec banks)]))
        offset (* 8 index)]
    {:index index :count banks :total (count ids) :offset offset
     :ids (subvec ids (min offset (count ids)) (min (+ offset 8) (count ids)))}))

(defn- parameter-at [state model encoder-index]
  (let [instance (get-in model [:instances (:selected-instance state)])
        id (nth (:ids (parameter-bank state instance)) encoder-index nil)]
    (when id
      {:instance-id (:id instance) :param id :encoder encoder-index
       :component (get-in state [:components [(:id instance) id]] 0)})))

(defn- touched [state model]
  (let [touch (get (:touches state) (peek (:touch-order state)))]
    (when (and touch (= (:selected-instance state) (:instance-id touch))
               (get-in model [:instances (:instance-id touch) :definition :params (:param touch)])) touch)))

(defn- edit-parameter [state model selection value mode]
  (let [{:keys [instance-id param component]} selection
        instance (get-in model [:instances instance-id])
        schema (get-in instance [:definition :params param])
        current (get-in instance [:params param])]
    (if (and schema (or (= mode :absolute) (not (zero? value))))
      (let [next-value (parameter-edit/edit schema current value
                                            {:mode mode :component component :fine? (:shift? state)})]
        {:state state :commands (if (= current next-value) []
                                    [{:op :param/set :instance-id instance-id :param param :value next-value}])})
      {:state state})))

(defn- touch-encoder [state model note]
  (if-let [selection (parameter-at state model note)]
    {:state (-> state (assoc-in [:touches note] selection)
                (update :touch-order #(conj (vec (remove #{note} %)) note)))}
    {:state state}))

(defn- release-encoder [state note]
  {:state (-> state (update :touches dissoc note)
              (update :touch-order #(vec (remove #{note} %))))})

(defn- page-control [state model direction]
  (if (:shift? state)
    (let [instance (get-in model [:instances (:selected-instance state)])
          bank (parameter-bank state instance)
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
        {:state state :commands [{:op :param/set :instance-id instance-id :param param
                                  :value (not (get-in instance [:params param]))}]}
        (let [next-component (mod (inc component) (count (parameter-edit/components schema)))]
          {:state (-> state (assoc-in [:components [instance-id param]] next-component)
                      (update :touches (fn [touches]
                                         (into {} (map (fn [[note touch]]
                                                         [note (if (= (select-keys touch [:instance-id :param])
                                                                      (select-keys selection [:instance-id :param]))
                                                                 (assoc touch :component next-component) touch)])) touches))))})))
    {:state state}))

(defn- picker-pad [state model note]
  (when-let [{:keys [instance-id param]} (touched state model)]
    (let [schema (get-in model [:instances instance-id :definition :params param])
          [x y] (codec/pad-coordinates note)
          value (case (:type schema)
                  :color (parameter-edit/color-grid-value x y)
                  :enum (nth (or (:values schema) (:options schema)) (+ x (* y 8)) ::missing)
                  ::missing)]
      (when (#{:color :enum} (:type schema))
        {:state state :commands (if (= ::missing value) []
                                    [{:op :param/set :instance-id instance-id :param param :value value}])}))))

(defn- press-pad [state event model envelope]
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
        (get-in state [:pads (:note event)]) {:state state}
        (= mode :held)
        (let [hold (bindings/begin-hold (:holds state) (:id cue) envelope)]
          {:state (-> state (assoc :holds (:state hold) :selected-cue (:id cue))
                      (update :pressed-pads conj note)
                      (assoc-in [:pads note] (:gesture-id hold)))
           :commands (mapv #(assoc % :launch launch-data :pad-note note) (:commands hold))})
        (and (= mode :persistent) active)
        {:state (-> state (assoc :selected-cue (:id cue) :selected-instance (:id active))
                    (update :pressed-pads disj note) (update :pad-instances dissoc note))
         :commands [{:op :instance/end :instance-id (:id active)
                     :force? (= :releasing (:phase active))}]}
        :else
        {:state (-> state (assoc :selected-cue (:id cue)) (update :pressed-pads conj note))
         :commands [{:op :cue/launch :cue-id (:id cue)
                     :pad-note note :launch launch-data}]}))
    {:state state}))

(defn- release-pad [state note envelope]
  (let [state (-> state (update :pressed-pads disj note) (update :pad-instances dissoc note))]
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

(defn- encoder [state event model]
  (edit-parameter state model (parameter-at state model (- (:controller event) 71))
                  (codec/signed-encoder (:raw-value event)) :relative))

(defn- input [device-id state event model envelope]
  (let [state (selected-state state model)]
   (cond
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
    {:state (assoc state :shift? (pos? (:raw-value event)))}
    (and (= :note-on (:type event)) (<= 0 (:note event) 7))
    (touch-encoder state model (:note event))
    (and (= :note-off (:type event)) (<= 0 (:note event) 7))
    (release-encoder state (:note event))
    (= :pitch-bend (:type event))
    (edit-parameter state model (touched state model) (:value event) :absolute)
    (and (= :control-change (:type event)) (pos? (:raw-value event)) (#{62 63} (:controller event)))
    (page-control state model (if (= 62 (:controller event)) -1 1))
    (and (= :control-change (:type event)) (pos? (:raw-value event)) (<= 20 (:controller event) 27))
    (component-button state model (- (:controller event) 20))
    (and (= :note-on (:type event)) (codec/pad-coordinates (:note event)))
    (or (picker-pad state model (:note event)) (press-pad state event model envelope))
    (= :note-off (:type event)) (release-pad state (:note event) envelope)
    (= :poly-pressure (:type event)) (pressure-pad state event model)
    (and (= :control-change (:type event)) (<= 71 (:controller event) 78))
    (encoder state event model)
    (and (= :control-change (:type event)) (= 79 (:controller event)))
    {:state state :commands [{:op :master/set
                              :value (bindings/clamp (+ (:master model)
                                                      (* 0.01 (codec/signed-encoder (:raw-value event)))) [0 1])}]}
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

(defn display-view
  "Device-independent labels/values. A display transport draws this map."
  [state model]
  (let [state (selected-state state model)
        instance (get-in model [:instances (:selected-instance state)])
        bank (parameter-bank state instance)
        active (views/active-instances model)
        active-index (or (first (keep-indexed #(when (= (:id instance) (:id %2)) %1) active)) 0)
        active-offset (* 8 (quot active-index 8))
        cue (get-in model [:registry :cues (:selected-cue state)])
        effect (or (:definition instance) (get-in model [:registry :effects (:effect-id cue)]))
        cue-view (when cue (views/cue-view model (:id cue)))]
    {:title "Tolglow" :page (:page-id state) :origin (:origin state)
     :status (or (:fault state) (if (:ready? state) :ready :loading-palettes))
     :master (:master model) :blackout? (:blackout? model)
     :bpm (get-in model [:transport :bpm])
     :selected (:selected-cue state)
     :epoch (:epoch model) :frame-number (:frame-number model)
     :instance-id (:id instance) :definition-version (:effect-version instance)
     :parameter-bank (dissoc bank :ids)
     :touched-parameter (touched state model)
     :fine? (boolean (:shift? state))
     :active-effect-navigation {:index active-index :count (count active) :offset active-offset}
     :active-effects (mapv #(select-keys % [:id :cue-id :effect-id :order :phase])
                           (take 8 (drop active-offset active)))
     :cue (when cue (select-keys cue-view [:id :name :color :active? :releasing?]))
     :effect (when effect (select-keys effect [:id :name :categories :modifiers :envelope]))
     :swatch (:color cue-view)
     :parameters (mapv (fn [k]
                         (let [schema (get-in effect [:params k])
                               component (get-in state [:components [(:id instance) k]] 0)]
                           {:id k :param k :name (or (:name schema) (name k))
                            :value (get-in instance [:params k]) :schema schema
                            :component component :component-label (nth (parameter-edit/components schema) component)
                            :preview-samples (:preview-samples schema)})) (:ids bank))
     :cells (mapv (fn [x] (when-let [cue (cue-at state model (codec/pad-note x 0))]
                            (views/cue-view model (:id cue)))) (range 8))
     :labels (mapv (fn [x] (some-> (cue-at state model (codec/pad-note x 0)) :id str)) (range 8))}))

(defn- feedback [device-id timeout-ms batch-size state model envelope]
  (let [state (selected-state state model)
        alive (set (keys (:instances model)))
        state (-> state (update :parameter-banks #(select-keys % alive))
                  (update :components #(into {} (filter (fn [[[id _] _]] (alive id))) %)))
        touch (touched state model)
        schema (get-in model [:instances (:instance-id touch) :definition :params (:param touch)])
        time (:time-ms envelope)
        waiting? (:awaiting-led-ack? state)
        timed-out? (and waiting? (>= (- time (:last-led-at-ms state time)) timeout-ms))
        state (cond
                (and (not (:ready? state)) (>= (- time (:palette-start-ms state time)) timeout-ms))
                (assoc state :fault :palette-timeout)
                (and timed-out? (>= (:led-retries state 0) 2))
                (assoc state :fault :led-timeout)
                timed-out? (-> state (assoc :awaiting-led-ack? false :last-leds {}) (update :led-retries (fnil inc 0)))
                :else state)
        display (display-view state model)
        display-changed? (not= display (:last-display state))
        state (assoc state :last-display display)
        desired (into {} (for [y (range 8) x (range 8)]
                           (let [cue (cue-at state model (codec/pad-note x y))]
                             [[x y] (case (:type schema)
                                      :color (mapv #(int (Math/round (* 255.0 %))) (parameter-edit/color-grid-value x y))
                                      :enum (let [value (nth (or (:values schema) (:options schema)) (+ x (* y 8)) ::missing)
                                                  selected (get-in model [:instances (:instance-id touch) :params (:param touch)])]
                                              (cond (= ::missing value) [0 0 0] (= selected value) [255 255 255] :else [30 70 120]))
                                      (if cue (rgb (views/cue-view model (:id cue))) [0 0 0]))])))
        changes (when (and (:ready? state) (nil? (:fault state)) (not (:awaiting-led-ack? state)))
                  (take batch-size (filter (fn [[xy color]] (not= color (get-in state [:last-leds xy])))
                                           (sort-by key desired))))
        messages (vec (mapcat (fn [[[x y] color]]
                               (codec/pad-led-messages device-id x y color
                                 (last (get-in state [:palettes (codec/pad-note x y)])))) changes))
        keepalive? (and (:ready? state) (nil? (:fault state)) (not (:awaiting-led-ack? state))
                        (empty? changes) (>= (- time (:last-led-at-ms state time)) (/ timeout-ms 2)))
        query? (or (seq changes) keepalive?)]
    (cond-> {:state (cond-> state
                     (seq changes) (update :last-leds into changes)
                     query? (assoc :awaiting-led-ack? true :last-led-at-ms time))
             :midi (cond-> messages query? (conj (codec/sysex device-id [0x09])))}
      display-changed? (assoc :display display)
      (:fault state) (assoc :lifecycle :disconnect))))

(defn- stop [device-id state _model _envelope disconnected?]
  {:state (assoc state :pads {} :holds {} :ready? false :last-leds {} :last-display nil
                       :touches {} :touch-order [] :shift? false :pressed-pads #{} :pad-instances {})
   :commands (mapv (fn [id] {:op :instance/end :instance-id id})
                   (keep :instance-id (vals (get-in state [:holds :gestures]))))
   :midi (if (or disconnected? (not (:ready? state))) []
             (into (vec (for [note (range 36 100)] [0x80 note 0]))
                   (map (fn [[index rgbw]] (codec/palette-write device-id index rgbw)))
                   (sort-by key (:palettes state))))})

(defn profile
  "Build a Push 2 profile with an explicitly known MIDI device-id and page-id.
  Sequential palette acquisition precedes writes; LEDs use acknowledged batches.
  Missing responses are reported on refresh!, never guessed."
  [{:keys [device-id page-id timeout-ms led-batch-size]
    :or {device-id 0 page-id :main timeout-ms 1500 led-batch-size 8}}]
  (codec/palette-request device-id 0)
  (when-not (and (number? timeout-ms) (pos? timeout-ms)
                 (integer? led-batch-size) (<= 1 led-batch-size 16))
    (throw (ex-info "Invalid Push 2 timeout/batch size" {})))
  (let [initial {:page-id page-id :origin [0 0] :palettes {} :next-palette 0
                 :ready? false :pads {} :holds {} :last-leds {} :led-retries 0
                 :parameter-banks {} :components {} :touches {} :touch-order [] :shift? false
                 :pressed-pads #{} :pad-instances {}}]
    {:id :push-2 :capabilities capabilities :initial-state initial
     :decode (partial decode device-id)
     :start (fn [state _model envelope]
              {:state (assoc state :palette-start-ms (:time-ms envelope))
               :midi [(codec/palette-request device-id 0)]})
     :input (partial input device-id)
     :feedback (partial feedback device-id timeout-ms led-batch-size)
     :stop (partial stop device-id)
     :resume-event? #(and (= :control-change (:type %)) (= 59 (:controller %)) (pos? (:raw-value %)))
     :reset-model #(assoc % :pads {} :holds {} :selected-instance nil :selected-cue nil :last-leds {}
                           :parameter-banks {} :components {} :touches {} :touch-order [] :shift? false
                           :pressed-pads #{} :pad-instances {})
     :ack (fn [state command ack]
            (let [hold (when-let [gesture (:gesture-id command)]
                         (bindings/acknowledge-hold (:holds state) gesture ack))]
              {:state (cond-> state
                        hold (assoc :holds (:state hold))
                        (and (= :cue/launch (:op command)) (= :accepted (:status ack)))
                        (assoc :selected-instance (:instance-id ack))
                        (and (= :cue/launch (:op command)) (= :accepted (:status ack))
                             (contains? (:pressed-pads state) (:pad-note command)))
                        (assoc-in [:pad-instances (:pad-note command)] (:instance-id ack)))
               :commands (:commands hold)}))}))

(defn connect!
  "REPL facade: options are session options plus :device-id/:page-id. Supply MIDI
  and optional display transports; no device is guessed or automatically bound."
  [options]
  (session/open! (session/create (assoc options :profile (profile options)))))

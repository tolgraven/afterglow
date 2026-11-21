(ns afterglow.control.devices.push-2
  "Composable Push 2 profile over the common command model. MIDI protocol comes
  from Afterglow's existing adapter; this module has no port or native UI access."
  (:require [afterglow.control.bindings :as bindings]
            [afterglow.control.codecs.midi :as midi]
            [afterglow.control.codecs.push-2 :as codec]
            [afterglow.control.views :as views]
            [afterglow.control.devices.session :as session]))

(def capabilities
  (assoc codec/capabilities :adapter :composable-session
         :implemented #{:pad-cues :held-release :page-scroll :parameter-encoders
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

(defn- press-pad [state event model envelope]
  (if-let [cue (cue-at state model (:note event))]
    (let [mode (or (:launch-mode cue) (when (:held cue) :held) :persistent)
          active (active-for-cue model (:id cue))]
      (cond
        (get-in state [:pads (:note event)]) {:state state}
        (= mode :held)
        (let [hold (bindings/begin-hold (:holds state) (:id cue) envelope)]
          {:state (-> state (assoc :holds (:state hold) :selected-cue (:id cue))
                      (assoc-in [:pads (:note event)] (:gesture-id hold)))
           :commands (:commands hold)})
        (and (= mode :persistent) active)
        {:state (assoc state :selected-cue (:id cue) :selected-instance (:id active))
         :commands [{:op :instance/end :instance-id (:id active)
                     :force? (= :releasing (:phase active))}]}
        :else
        {:state (assoc state :selected-cue (:id cue))
         :commands [{:op :cue/launch :cue-id (:id cue)
                     :launch {:mode mode :velocity (:value event)}}]}))
    {:state state}))

(defn- release-pad [state note envelope]
  (if-let [gesture (get-in state [:pads note])]
    (let [release (bindings/end-hold (:holds state) gesture envelope)]
      {:state (-> state (assoc :holds (:state release)) (update :pads dissoc note))
       :commands (:commands release)})
    {:state state}))

(defn- encoder [state event model]
  (let [delta (codec/signed-encoder (:raw-value event))
        instance (get-in model [:instances (:selected-instance state)])
        parameter (nth (sort-by str (keys (get-in instance [:definition :params])))
                       (- (:controller event) 71) nil)
        schema (get-in instance [:definition :params parameter])
        value (get-in instance [:params parameter])]
    (if (and instance (#{:number :integer} (:type schema))
             (number? value) (:bounds schema))
      (let [[low high] (:bounds schema)
            step (if (= :integer (:type schema)) 1 (/ (- high low) 100.0))
            next-value (bindings/clamp (+ value (* delta step)) [low high])]
        {:state state :commands [{:op :param/set :instance-id (:id instance)
                                  :param parameter :value next-value}]})
      {:state state})))

(defn- input [device-id state event model envelope]
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
    (and (= :note-on (:type event)) (codec/pad-coordinates (:note event)))
    (press-pad state event model envelope)
    (= :note-off (:type event)) (release-pad state (:note event) envelope)
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
    :else {:state state}))

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
  (let [instance (get-in model [:instances (:selected-instance state)])
        cue (get-in model [:registry :cues (:selected-cue state)])
        effect (or (:definition instance) (get-in model [:registry :effects (:effect-id cue)]))
        cue-view (when cue (views/cue-view model (:id cue)))]
    {:title "Tolglow" :page (:page-id state) :origin (:origin state)
     :status (or (:fault state) (if (:ready? state) :ready :loading-palettes))
     :master (:master model) :blackout? (:blackout? model)
     :bpm (get-in model [:transport :bpm])
     :selected (:selected-cue state)
     :cue (when cue (select-keys cue-view [:id :name :color :active? :releasing?]))
     :effect (when effect (select-keys effect [:id :name :categories :modifiers :envelope]))
     :swatch (:color cue-view)
     :parameters (mapv (fn [[k v]] {:id k :param k :name (or (get-in effect [:params k :name]) (name k))
                                   :value v :schema (get-in effect [:params k])
                                   :preview-samples (get-in effect [:params k :preview-samples])})
                       (sort-by (comp str key) (:params instance)))
     :cells (mapv (fn [x] (when-let [cue (cue-at state model (codec/pad-note x 0))]
                            (views/cue-view model (:id cue)))) (range 8))
     :labels (mapv (fn [x] (some-> (cue-at state model (codec/pad-note x 0)) :id str)) (range 8))}))

(defn- feedback [device-id timeout-ms batch-size state model envelope]
  (let [time (:time-ms envelope)
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
                             [[x y] (if cue (rgb (views/cue-view model (:id cue))) [0 0 0])])))
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
  {:state (assoc state :pads {} :holds {} :ready? false :last-leds {} :last-display nil)
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
                 :ready? false :pads {} :holds {} :last-leds {} :led-retries 0}]
    {:id :push-2 :capabilities capabilities :initial-state initial
     :decode (partial decode device-id)
     :start (fn [state _model envelope]
              {:state (assoc state :palette-start-ms (:time-ms envelope))
               :midi [(codec/palette-request device-id 0)]})
     :input (partial input device-id)
     :feedback (partial feedback device-id timeout-ms led-batch-size)
     :stop (partial stop device-id)
     :resume-event? #(and (= :control-change (:type %)) (= 59 (:controller %)) (pos? (:raw-value %)))
     :reset-model #(assoc % :pads {} :holds {} :selected-instance nil :selected-cue nil :last-leds {})
     :ack (fn [state command ack]
            (let [hold (when-let [gesture (:gesture-id command)]
                         (bindings/acknowledge-hold (:holds state) gesture ack))]
              {:state (cond-> state
                        hold (assoc :holds (:state hold))
                        (and (= :cue/launch (:op command)) (= :accepted (:status ack)))
                        (assoc :selected-instance (:instance-id ack)))
               :commands (:commands hold)}))}))

(defn connect!
  "REPL facade: options are session options plus :device-id/:page-id. Supply MIDI
  and optional display transports; no device is guessed or automatically bound."
  [options]
  (session/open! (session/create (assoc options :profile (profile options)))))

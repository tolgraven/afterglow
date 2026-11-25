(ns afterglow.control.devices.push-cue-gesture-test
  (:require [clojure.test :refer [deftest is testing]]
            [afterglow.control.codecs.mpe :as mpe]
            [afterglow.control.codecs.push-3 :as push-3]
            [afterglow.control.devices.push-cue-gesture :as gesture]
            [afterglow.control.model :as model]
            [afterglow.control.quantization :as queue]))

(defn- show []
  (model/new-show
    {:show-id :gesture-show
     :registry {:effects {:plain {:id :plain :version 1 :params {}}
                          :wash {:id :wash :version 1
                                 :params {:level {:type :number :bounds [0 1] :default 0.5}
                                          :color {:type :color :default [0.2 0.3 0.4]}
                                          :xyz {:type :vector :size 3 :bounds [-2 2] :default [0 0 0]}
                                          :speed {:type :number :bounds [0 10] :default 5 :velocity true
                                                  :velocity-min 8 :velocity-max 2}}}}
                :cues {:plain {:id :plain :version 1 :effect-id :plain}
                       :wash {:id :wash :version 1 :effect-id :wash}
                       :wash-2 {:id :wash-2 :version 1 :effect-id :wash}
                       :other {:id :other :version 1 :effect-id :plain}
                       :shot {:id :shot :version 1 :effect-id :plain :launch-mode :one-shot :duration-ms 120}}}
     :pages {:main {:id :main :cells {[0 0] :plain [1 0] :wash [2 0] :shot [3 0] :other [4 0] :wash-2}}
             :second {:id :second :cells {[0 0] :other [1 0] :plain}}}}))

(defn- envelope [show id ms]
  (merge (select-keys show [:show-id :epoch]) {:command-id id :time-ms ms :source {:session-id :pad-test}}))

(defn- apply-command [show id ms command]
  (model/apply-command show (merge command (envelope show id ms))))

(defn- run-event
  ([options state show token ms event] (run-event options state show token ms event {}))
  ([options state show token ms event surface]
   (gesture/step options state event surface show (envelope show token ms))))

(defn- pad [key cell pressed?]
  {:type :pad :gesture-key key :cell cell :pressed? pressed? :value 0.75})

(defn- axis [key kind value]
  {:type :axis :gesture-key key :axis kind :value value})

(defn- launch [show id ms cue-id]
  (apply-command show id ms {:op :cue/launch :cue-id cue-id}))

(deftest tap-and-hold-each-launch-once
  (let [options (gesture/configure {:hold-ms 100})
        show (show) key [3 36]
        press (run-event options (gesture/initial-state) show "pad-a" 10 (pad key [0 0] true))
        repeat (run-event options (:state press) show "repeat" 11 (pad key [1 0] true))
        early-tick (run-event options (:state repeat) show "my-tick" 109 {:type :tick})]
    (is (= 110 (gesture/next-deadline-ms (:state press))))
    (is (= (:state press) (:state repeat)))
    (is (empty? (:commands early-tick)))
    (testing "A short tap becomes persistent at release"
      (let [tap (run-event options (:state early-tick) show "release" 109 (pad key [0 0] false))
            command (first (:commands tap))
            launched (model/apply-command show command)]
        (is (= 1 (count (:commands tap))))
        (is (= :persistent (get-in command [:launch :mode])))
        (is (= 109 (get-in launched [:model :instances "0:1" :started-at-ms])))
        (is (nil? (gesture/next-deadline-ms (:state tap))))))
    (testing "A hold starts at the deadline, and note-off releases that instance"
      (let [held (run-event options (:state early-tick) show "my-tick" 110 {:type :tick})
            command (first (:commands held))
            {launched :model ack :ack} (model/apply-command show command)
            state (:state (gesture/acknowledge (:state held) command ack))
            tick (run-event options state launched "later-tick" 111 {:type :tick})
            release (run-event options (:state tick) launched "note-off" 240 (pad key [0 0] false))
            ended (apply-command launched "end-held" 240 (first (:commands release)))]
        (is (= :held (get-in command [:launch :mode])))
        (is (= 110 (get-in launched [:instances "0:1" :started-at-ms])))
        (is (empty? (:commands tick)))
        (is (= "0:1" (-> release :commands first :instance-id)))
        (is (= :releasing (get-in ended [:model :instances "0:1" :phase])))
        (is (= 1 (count (get-in ended [:model :instances]))))))
    (testing "A missed timer and a synthetic retrigger never become a tap"
      (is (empty? (:commands (run-event options (:state press) show "late-off" 110 (pad key [0 0] false)))))
      (is (empty? (:commands (run-event options (:state press) show "retrigger" 15
                                       (assoc (pad key [0 0] false) :cancelled? true))))))))

(deftest active-expression-is-per-note-and-taps-use-the-captured-instance
  (let [options (gesture/configure {:hold-ms 100 :axes #{:strike :pressure :glide :slide}
                                    :param-mappings {:color {:axis :glide :component 0}
                                                     :xyz {:axis :slide :component 2}}})
        started (launch (show) "wash-1" 0 :wash)
        show (:model started) owner (get-in started [:ack :instance-id])
        state (:state (run-event options (gesture/initial-state) show "press" 10 (pad [2 46 1] [1 0] true)))
        pressed-neighbor (run-event options state show "other-press" 20 (pad [3 47 1] [3 0] true))
        before-hold (run-event options (:state pressed-neighbor) show "pressure" 111 (axis [2 46 1] :pressure 1))
        hold (run-event options (:state before-hold) show "tick" 111 {:type :tick})
        pressure (run-event options (:state hold) show "pressure" 112 (axis [2 46 1] :pressure 1))
        glide (run-event options (:state pressure) show "glide" 113 (axis [2 46 1] :glide 1))
        slide (run-event options (:state glide) show "slide" 114 (axis [2 46 1] :slide 1))]
    (is (empty? (:commands before-hold)))
    (is (= 110 (gesture/next-deadline-ms (:state before-hold))))
    (is (empty? (:commands hold)))
    (is (= [[:level 1.0] [:color [1.0 0.3 0.4]] [:xyz [0 0 2.0]]]
           (mapv (juxt :param :value) (mapcat :commands [pressure glide slide]))))
    (is (= [owner owner owner] (mapv :instance-id (mapcat :commands [pressure glide slide]))))
    (is (empty? (:commands (run-event options (:state slide) show "neighbor" 115 (axis [3 47 1] :pressure 1)))))
    (let [release (run-event options (:state slide) show "off" 120 (pad [2 46 1] [1 0] false))]
      (is (empty? (:commands release)))
      (is (empty? (:commands (run-event options (:state release) show "late-axis" 121 (axis [2 46 1] :slide 1)))))
      (is (= 120 (gesture/next-deadline-ms (:state release)))))
    (let [replacement (:model (launch show "wash-replacement" 15 :wash))
          tap (run-event options state replacement "off" 20 (pad [2 46 1] [1 0] false))
          result (apply-command replacement "tap-end" 20 (first (:commands tap)))
          removed (:model (apply-command replacement "remove-original" 18 {:op :instance/remove :instance-id owner}))]
      (is (= owner (-> tap :commands first :instance-id)))
      (is (= :running (get-in result [:model :instances "0:2" :phase])))
      (is (empty? (:commands (run-event options state removed "off" 20 (pad [2 46 1] [1 0] false))))))))

(deftest captured-modifier-selects-active-and-makes-expressive-idle-gestures-reachable
  (let [layout (push-3/compile-layout {:buttons {:gesture-phone {:channel 7 :controller 26}
                                                :fine {:channel 5 :controller 90}}
                                       :pads {[1 0] {:channel 8 :note 25}}})
        pressed (fn [bytes] #{(:control-id (push-3/decode layout bytes))})
        options (gesture/configure {:hold-ms 100 :gesture-modifier :cue-edit
                                    :button-bindings {:gesture-phone :cue-edit :fine :shift}})
        modifier {:pressed-buttons (pressed [0xb7 26 127])}
        fine {:pressed-buttons (pressed [0xb5 90 127])}
        pad-event (assoc (push-3/decode layout [0x98 25 64]) :cell [1 0])
        empty (show)
        start (launch empty "launch" 0 :wash)
        selected (run-event options (gesture/initial-state) (:model start) "select" 10 pad-event modifier)
        pending (run-event options (gesture/initial-state) empty "modified" 10 pad-event modifier)]
    (is (empty? (:commands selected)))
    (is (= (get-in start [:ack :instance-id]) (get-in selected [:state :selection :instance-id])))
    (is (nil? (gesture/next-deadline-ms (:state selected))))
    (is (empty? (:commands (run-event options (:state selected) (:model start) "release" 15
                                     (assoc pad-event :pressed? false) modifier))))
    (is (= :persistent (-> (run-event options (gesture/initial-state) empty "fine" 10 pad-event fine)
                           :commands first :launch :mode)))
    (is (= 110 (gesture/next-deadline-ms (:state pending))))
    (is (= :persistent (-> (run-event options (:state pending) empty "release" 11 (assoc pad-event :pressed? false))
                           :commands first :launch :mode)))
    (is (empty? (:commands (run-event options (gesture/initial-state) empty "editor" 10 pad-event
                                     (assoc modifier :pad-owner :editor)))))
    (is (true? (:pass-through? (run-event options (gesture/initial-state) empty "picker" 10 pad-event
                                          (assoc modifier :pad-owner :target-picker)))))
    (let [target (run-event options (gesture/initial-state) (:model start) "target" 10 pad-event
                            {:target-selector {:kind :group :id :fixtures}})]
      (is (true? (:target-consumed? target)))
      (is (= {:kind :group :id :fixtures} (-> target :commands first :launch :selector))))
    (let [shot (run-event options (gesture/initial-state) empty "shot" 10 (pad [8 27] [2 0] true) modifier)
          command (first (:commands shot))
          started (model/apply-command empty command)]
      (is (= :one-shot (get-in command [:launch :mode])))
      (is (= 120 (get-in started [:model :instances "0:1" :duration-ms])))
      (is (empty? (:commands (run-event options (:state shot) (:model started) "release" 12 (pad [8 27] [2 0] false))))))))

(deftest queued-holds-cancel-by-launch-id-and-page-changes-fence-late-feedback
  (let [options (gesture/configure {:launch-grid {:beats 1} :hold-ms 100})
        show (show) key [2 36]
        clock {:clock-epoch 0 :time-ms 111 :beat 0.21 :playing? true}
        pressed (run-event options (gesture/initial-state) show "hold" 10 (pad key [0 0] true))
        held (run-event options (:state pressed) show "deadline" 110 {:type :tick})
        command (first (:commands held))
        admitted (queue/admit (queue/new-state) {:command command :grid (:grid command) :raw (:raw command)} clock)
        pending (:state (gesture/acknowledge (:state held) command (:receipt admitted)))
        moved (run-event options pending show "new-page" 112 {:type :context} {:page-id :second})
        release (run-event options (:state moved) show "release" 113 (pad key [0 0] false) {:page-id :second :pad-owner :editor})
        cancel (first (:commands release))
        cancelled (queue/cancel (:state admitted) (:launch-command-id cancel) 0 (:reason cancel))]
    (is (= {:beats 1} (:grid command)))
    (is (= {:time-ms 10} (:raw command)))
    (is (= :pending (get-in admitted [:receipt :status])))
    (is (= "hold" (:launch-command-id cancel)))
    (is (= :cue/cancel-launch (:op cancel)))
    (is (= :cancelled (get-in cancelled [:receipt :status])))
    (is (empty? (:due (queue/tick (:state cancelled) (assoc clock :beat 1 :time-ms 500)))))
    (let [tap (run-event options (:state pressed) show "tap" 90 (pad key [0 0] false))
          command (first (:commands tap))
          queued (queue/admit (queue/new-state) {:command command :grid (:grid command)} clock)
          tick (queue/tick (:state queued) (assoc clock :beat 1 :time-ms 500))
          fired (apply-command show "hold" 500 (-> tick :due first :command))
          settled (queue/settle (:state tick) "hold" (assoc clock :beat 1 :time-ms 500) true (:ack fired))
          moved (run-event options (:state tap) (:model fired) "page" 501 {:type :context} {:page-id :second})
          next-pad (run-event options (:state moved) (:model fired) "next-pad" 502 (pad key [0 0] true) {:page-id :second})
          late (gesture/acknowledge (:state next-pad) command (:receipt settled))]
      (is (= :persistent (get-in fired [:model :instances "0:1" :launch-mode])))
      (is (= :fired (get-in settled [:receipt :status])))
      (is (= :other (get-in late [:state :selection :cue-id])))
      (is (nil? (get-in late [:state :pads key :instance-id]))))
    (let [moved (run-event options (:state pressed) show "new-page" 40 {:type :context} {:page-id :second})
          returned (run-event options (:state moved) show "original-page" 50 {:type :context})]
      (is (empty? (:commands (run-event options (:state returned) show "release" 90 (pad key [0 0] false))))))))

(deftest late-immediate-receipts-honor-early-release-and-show-epochs
  (let [options (gesture/configure {:hold-ms 100})
        show (show) key [2 36]
        pressed (run-event options (gesture/initial-state) show "press" 10 (pad key [0 0] true))
        held (run-event options (:state pressed) show "tick" 110 {:type :tick})
        command (first (:commands held))
        {launched :model ack :ack} (model/apply-command show command)
        release (run-event options (:state held) show "release" 125 (pad key [0 0] false))
        late (gesture/acknowledge (:state release) command ack)
        duplicate (gesture/acknowledge (:state late) command ack)
        reset-show (:model (apply-command launched "restart" 130 {:op :show/restart}))
        reset-state (:state (run-event options (:state release) reset-show "reset" 130 {:type :context}))]
    (is (empty? (:commands release)))
    (is (= "0:1" (-> late :commands first :instance-id)))
    (is (empty? (:commands duplicate)))
    (is (empty? (:commands (gesture/acknowledge reset-state command ack))))
    (is (empty? (:commands (gesture/stop (:state held) (envelope reset-show "close" 131)))))))

(deftest preserve-push-2-velocity-and-let-policy-disable-individual-axes
  (let [options (gesture/configure {:legacy-velocity? true})
        show (show) key [0 37]
        pressed (run-event options (gesture/initial-state) show "strike" 0 (pad key [1 0] true))
        command (first (:commands pressed))
        {launched :model ack :ack} (model/apply-command show command)
        state (:state (gesture/acknowledge (:state pressed) command ack))
        pressure (run-event options state launched "pressure" 1 (axis key :pressure 0.25))
        off (gesture/configure {:legacy-velocity? true :mapping-policy {:disabled-axes ["strike" "pressure"]}})
        disabled (run-event off (gesture/initial-state) show "off" 0 (pad key [1 0] true))]
    (is (= 3.5 (get-in command [:launch :params :speed])))
    (is (= {:speed 6.5 :level 0.25} (into {} (map (juxt :param :value)) (:commands pressure))))
    (is (empty? (:commands disabled)))
    (is (some? (gesture/next-deadline-ms (:state disabled))))))

(deftest decoded-mpe-member-expression-follows-the-complete-voice-id
  (let [options (gesture/configure {:hold-ms 100 :axes #{:strike :pressure :glide :slide}})
        zone (mpe/compile-zone {:manager-channel 0 :member-channels [1 2]})
        cells {40 [1 0] 41 [4 0]}
        a (launch (show) "wash-a" 0 :wash)
        b (launch (:model a) "wash-b" 0 :wash-2)
        show (:model b)
        deliver (fn [{:keys [state decoder]} ms bytes]
                  (let [{decoder :state events :events} (mpe/advance zone decoder bytes)]
                    (reduce (fn [{:keys [state commands]} {:keys [type note voice-id axes axis value reason]}]
                              (let [event (case type
                                            (:note-on :note-off) {:type :pad :gesture-key voice-id :cell (cells note)
                                                                  :pressed? (= :note-on type) :axes axes
                                                                  :cancelled? (and (= :note-off type) (not= :released reason))}
                                            :axis {:type :axis :gesture-key voice-id :axis axis :value value}
                                            {:type :context})
                                    result (run-event options state show (str "mpe-" ms) ms event)]
                                {:state (:state result) :decoder decoder :commands (into commands (:commands result))}))
                            {:state state :decoder decoder :commands []} events)))
        first-press (deliver {:state (gesture/initial-state) :decoder (mpe/initial-state)} 10 [0x91 40 80])
        second-press (deliver first-press 11 [0x92 41 85])
        pending-pressure (deliver second-press 109 [0xd2 110])
        armed (merge pending-pressure (run-event options (:state pending-pressure) show "tick" 111 {:type :tick}))
        pressure-a (deliver armed 112 [0xd1 127])
        pressure-b (deliver pressure-a 113 [0xd2 0])
        released-a (deliver pressure-b 114 [0x81 40 0])]
    (is (empty? (:commands pending-pressure)))
    (is (= (get-in a [:ack :instance-id]) (-> pressure-a :commands first :instance-id)))
    (is (= (get-in b [:ack :instance-id]) (-> pressure-b :commands first :instance-id)))
    (is (empty? (:commands released-a)))
    (is (empty? (:commands (deliver released-a 115 [0xd1 80]))))
    (is (= (get-in b [:ack :instance-id]) (-> (deliver released-a 116 [0xd2 80]) :commands first :instance-id)))))

(ns afterglow.control.devices.push-3-cue-gestures-test
  (:require [afterglow.control.devices.push-3 :as push]
            [afterglow.control.devices.session :as session]
            [afterglow.control.model :as model]
            [afterglow.control.quantization :as quantization]
            [clojure.test :refer [deftest is]]))

(defn- show []
  (model/new-show
    {:show-id :push-test
     :registry {:effects {:plain {:id :plain :version 1 :params {}}
                          :color {:id :color :version 1
                                  :params {:level {:type :number :bounds [0 1] :default 0.5}
                                           :color {:type :color :default [0.1 0.2 0.3]}
                                           :position {:type :vector :bounds [-2 2] :size 3 :default [0 0 0]}}}}
                :cues {:plain {:id :plain :version 1 :effect-id :plain}
                       :held {:id :held :version 1 :effect-id :plain}
                       :wash {:id :wash :version 1 :effect-id :color}
                       :wash-b {:id :wash-b :version 1 :effect-id :color}
                       :shot {:id :shot :version 1 :effect-id :plain :launch-mode :one-shot :duration-ms 80}}}
     :pages {:main {:id :main :cells {[0 0] :plain [1 0] :wash [2 0] :wash-b [3 0] :shot [4 0] :held}}}}))

(def ^:private base-options
  {:user-mode? true :expression-mode :poly-aftertouch :cue-gestures? true :hold-ms 100
   :layout {:pads {[0 0] {:channel 3 :note 12} [1 0] {:channel 3 :note 13}
                   [2 0] {:channel 3 :note 14} [3 0] {:channel 3 :note 15} [4 0] {:channel 3 :note 16}}
            :encoder-touches {:color {:channel 3 :note 9}}
            :encoders {:level {:channel 3 :controller 19}}
            :buttons {:choose {:channel 5 :controller 42} :right {:channel 4 :controller 23}}}
   :encoder-bindings {:level {:param :level}}
   :button-bindings {:choose :choose-cue :right :page-right}
   :gesture-modifier :choose-cue})

(defn- command [show id time-ms body]
  (model/apply-command show (merge (select-keys show [:show-id :epoch])
                                   {:command-id id :source :test :time-ms time-ms} body)))

(defn- harness [overrides]
  (let [time (atom 0) show (atom (show)) log (atom []) receive (atom nil)
        refresh (atom nil) cancelled (atom 0)
        dispatch! (fn [cmd]
                    (swap! log conj cmd)
                    (let [result (model/apply-command @show cmd)]
                      (reset! show (:model result)) result))
        options (merge base-options
                       {:session-id :gesture-capture :model! #(deref show) :now-ms! #(deref time)
                        :dispatch! dispatch!
                        :schedule! (fn [tick] (reset! refresh tick) #(swap! cancelled inc))
                        :midi {:open! #(do (reset! receive %) :capture) :close! (fn [_])}}
                       overrides)]
    {:options options :time time :show show :log log :receive receive :refresh refresh :cancelled cancelled
     :input! (fn [at bytes] (reset! time at) (@receive bytes))
     :tick! (fn [at] (reset! time at) (@refresh))}))

(deftest user-mode-session-classifies-taps-and-holds-without-a-display
  (let [{:keys [options show log input! tick! cancelled]} (harness {})
        device (push/connect! options)]
    (try
      (input! 10 [0x93 12 96])
      (input! 20 [0xa3 12 127])
      (is (empty? @log))
      (input! 50 [0x83 12 0])
      (let [instance (get-in @show [:instances "0:1"])]
        (is (= :persistent (:launch-mode instance)))
        (is (= 50 (:started-at-ms instance)))
        (input! 60 [0x93 12 96])
        (is (= :running (get-in @show [:instances "0:1" :phase])))
        (input! 65 [0x83 12 0])
        (is (= "0:1" (:instance-id (last @log))))
        (is (= :releasing (get-in @show [:instances "0:1" :phase]))))
      (input! 70 [0x93 16 73])
      (tick! 169)
      (input! 170 [0xa3 16 127])
      (is (= 2 (count @log)))
      (tick! 170)
      (is (= :held (get-in @show [:instances "0:2" :launch-mode])))
      (is (= 170 (get-in @show [:instances "0:2" :started-at-ms])))
      (tick! 175)
      (is (= 3 (count @log)))
      (input! 181 [0x83 16 0])
      (is (= "0:2" (:instance-id (last @log))))
      (is (= :releasing (get-in @show [:instances "0:2" :phase])))
      (input! 190 [0x93 15 100])
      (is (= :one-shot (get-in @show [:instances "0:3" :launch-mode])))
      (is (= 80 (get-in @show [:instances "0:3" :duration-ms])))
      (input! 195 [0x83 15 0])
      (is (= :cue/launch (:op (last @log))))
      (is (empty? (:errors (session/snapshot device))))
      (finally (session/close! device)))
    (is (= 1 @cancelled))))

(deftest selected-edit-and-page-change-retain-exact-note-ownership
  (let [{:keys [options show log input! tick!]} (harness {})
        device (push/connect! options)]
    (try
      (swap! show #(-> (command % "outside-wash" 0 {:op :cue/launch :cue-id :wash}) :model))
      (input! 10 [0xb5 42 127])
      (input! 11 [0x93 13 96])
      (is (= "0:1" (:selected-instance (push/control-view (:local (session/snapshot device)) @show))))
      (input! 12 [0xa3 13 127])
      (input! 13 [0x83 13 0])
      (input! 14 [0xb5 42 0])
      (is (empty? @log))
      (input! 15 [0xb3 19 2])
      (is (= [:param/set "0:1" :level] ((juxt :op :instance-id :param) (last @log))))
      (input! 20 [0x93 12 96])
      (input! 21 [0xb4 23 127])
      (input! 22 [0x83 12 0])
      (tick! 122)
      (is (= [:param/set] (mapv :op @log)))
      (is (= [8 0] (:origin (push/control-view (:local (session/snapshot device)) @show))))
      (is (empty? (:errors (session/snapshot device))))
      (finally (session/close! device)))))

(deftest mpe-session-routes-active-expression-and-compound-editor-by-voice
  (let [{:keys [options show log input! tick!]}
        (harness {:expression-mode :mpe :zone {:manager-channel 0 :member-channels [1 2]}
                  :mpe-note-cells {40 [1 0] 41 [2 0]}
                  :encoder-bindings {:level {:param :level}}
                  :param-mappings {:position [{:axis :glide :component 0} {:axis :slide :component 2}]}})
        options (-> options (assoc-in [:layout :encoders :color] {:channel 3 :controller 18})
                    (assoc-in [:encoder-bindings :color] {:param :color}))
        device (push/connect! options)]
    (try
      (swap! show #(-> (command % "outside-a" 0 {:op :cue/launch :cue-id :wash}) :model
                       (command "outside-b" 0 {:op :cue/launch :cue-id :wash-b}) :model))
      (input! 10 [0x91 40 96])
      (input! 15 [0x92 41 64])
      (input! 109 [0xd1 127])
      (input! 110 [0xe1 127 127])
      (is (empty? @log))
      (tick! 115)
      (input! 116 [0xd1 127])
      (input! 117 [0xe1 127 127])
      (input! 118 [0xb2 74 0])
      (is (= [["0:1" :level 1.0] ["0:1" :position [2.0 0 0]] ["0:2" :position [0 0 -2.0]]]
             (mapv (juxt :instance-id :param :value) @log)))
      (input! 119 [0x81 40 0])
      (input! 120 [0x82 41 0])
      (is (every? #(= :running (:phase %)) (vals (:instances @show))))
      (input! 130 [0xb5 42 127])
      (input! 131 [0x92 41 90])
      (input! 132 [0x82 41 0])
      (input! 133 [0xb5 42 0])
      (input! 134 [0x93 9 127])
      (is (= :color (get-in (push/control-view (:local (session/snapshot device)) @show) [:pad-overlay :type])))
      (input! 135 [0x91 40 90])
      (input! 136 [0xb1 74 68])
      (input! 137 [0x83 9 0])
      (input! 138 [0x81 40 0])
      (is (= 4 (count @log)))
      (is (= [:param/set "0:2" :color] ((juxt :op :instance-id :param) (last @log))))
      (is (nil? (:pad-overlay (push/control-view (:local (session/snapshot device)) @show))))
      (is (empty? (:errors (session/snapshot device))))
      (finally (session/close! device)))))

(deftest quantized-session-keeps-strike-time-and-cancels-by-launch-id
  (let [pending (atom (quantization/new-state))
        timing-log (atom [])
        dispatch! (fn [{:keys [op grid raw time-ms launch-command-id reason] :as command}]
                    (swap! timing-log conj command)
                    (let [clock {:clock-epoch 0 :playing? true :time-ms time-ms :beat (/ time-ms 500)}
                          result (case op
                                   :cue/launch (quantization/admit @pending {:command command :grid grid :raw raw} clock)
                                   :cue/cancel-launch (quantization/cancel @pending launch-command-id 0 reason))]
                      (reset! pending (:state result))
                      (:receipt result)))
        {:keys [options input! tick!]} (harness {:dispatch! dispatch! :launch-grid {:beats 1}})
        device (push/connect! options)]
    (try
      (input! 10 [0x93 12 96])
      (input! 20 [0x83 12 0])
      (input! 30 [0x93 16 73])
      (tick! 130)
      (input! 135 [0x83 16 0])
      (let [[tap hold release] @timing-log]
        (is (= [{:time-ms 10} {:time-ms 30}] (mapv :raw [tap hold])))
        (is (= [20 130 135] (mapv :time-ms @timing-log)))
        (is (= (mapv :command-id [tap]) (mapv :command-id (quantization/pending @pending))))
        (is (= (:command-id hold) (:launch-command-id release)))
        (is (= :cancelled (:status (quantization/receipt @pending (:command-id hold)))))
        (is (not= (:command-id tap) (:command-id hold))))
      (is (empty? (:errors (session/snapshot device))))
      (finally (session/close! device)))))

(deftest default-connection-owns-a-clock-driven-cadence-and-reset-fences-old-deadlines
  (let [{:keys [options show log input! time]} (harness {})
        settled (promise)
        dispatch! (:dispatch! options)
        options (-> options (dissoc :schedule!)
                    (assoc :dispatch! (fn [cmd]
                                        (let [result (dispatch! cmd)]
                                          (when (= :cue/launch (:op cmd)) (deliver settled cmd))
                                          result))))
        device (push/connect! options)]
    (try
      (input! 10 [0x93 12 96])
      (swap! show #(-> (command % "restart" 20 {:op :show/restart}) :model))
      (reset! time 111)
      (session/refresh! device)
      (is (empty? @log))
      (input! 120 [0x83 12 0])
      (input! 130 [0x93 16 96])
      (reset! time 230)
      (let [launched (deref settled 2000 ::timeout)]
        (is (= :held (get-in launched [:launch :mode])))
        (is (= [1 230] ((juxt :epoch :time-ms) launched))))
      (is (empty? (:errors (session/snapshot device))))
      (finally (session/close! device)))
    (is (= :closed (:status (session/snapshot device))))))

(deftest deadlines-use-committed-model-before-display-projection
  (let [overrides {:display {:device :push-3 :input :view :open! (constantly :display)
                             :render! (fn [_ _]) :close! (fn [_])}
                   :feedback-source {:open! (constantly :feedback) :close! (fn [_])
                                     :project! (fn [_ _ model]
                                                 (assoc-in model [:pages :main :cells [0 0]] :shot))}}
        {:keys [options show input! tick!]} (harness overrides)
        device (push/connect! options)]
    (try
      (input! 10 [0x93 12 96])
      (tick! 110)
      (is (= :plain (get-in @show [:instances "0:1" :cue-id])))
      (is (= :held (get-in @show [:instances "0:1" :launch-mode])))
      (is (empty? (:errors (session/snapshot device))))
      (finally (session/close! device)))))

(deftest recreating-a-session-id-keeps-launch-commands-distinct
  (let [{:keys [options show log input!]} (harness {})]
    (dotimes [_ 2]
      (let [device (push/connect! options)]
        (try (input! 10 [0x93 15 96])
             (finally (session/close! device)))))
    (is (= 2 (count (distinct (map :command-id @log)))))
    (is (= [:one-shot :one-shot] (mapv :launch-mode (vals (:instances @show)))))))

(deftest captured-show-is-checked-again-before-admitting-an-active-tap
  (let [{:keys [options show log input!]} (harness {})
        armed? (atom false)
        reads (atom 0)
        device (push/connect! (assoc options :model!
                                     (fn []
                                       (when (and @armed? (= 2 (swap! reads inc)))
                                         (swap! show assoc :show-id :replacement))
                                       @show)))]
    (try
      (swap! show #(-> (command % "outside-wash" 0 {:op :cue/launch :cue-id :wash}) :model))
      (input! 10 [0x93 13 96])
      (reset! armed? true)
      (input! 15 [0x83 13 0])
      (is (= :replacement (:show-id @show)))
      (is (empty? @log))
      (is (= :running (get-in @show [:instances "0:1" :phase])))
      (is (= :stale-epoch (get-in (session/snapshot device) [:last-ack :reason])))
      (finally (session/close! device)))))

(deftest active-cue-selection-fences-an-existing-opacity-strip-contact
  (let [{:keys [options show log input!]} (harness {})
        options (-> options (assoc-in [:layout :touch-strip] {:channel 5})
                    (assoc-in [:layout :touch-strip-touch] {:channel 6 :note 24}))
        device (push/connect! options)]
    (try
      (swap! show #(-> (command % "outside-a" 0 {:op :cue/launch :cue-id :wash}) :model
                       (command "outside-b" 0 {:op :cue/launch :cue-id :wash-b}) :model))
      (input! 10 [0xb5 42 127])
      (input! 11 [0x93 13 96])
      (input! 12 [0x83 13 0])
      (input! 13 [0x96 24 127])
      (input! 14 [0x93 14 96])
      (input! 15 [0x83 14 0])
      (input! 16 [0xe5 0 0])
      (is (empty? @log))
      (input! 17 [0x86 24 0])
      (input! 18 [0x96 24 127])
      (input! 19 [0xe5 0 0])
      (is (= [[:instance/opacity-set "0:2" 0.0]] (mapv (juxt :op :instance-id :value) @log)))
      (is (empty? (:errors (session/snapshot device))))
      (finally (session/close! device)))))

(ns push-cue-gesture-replay-543
  (:require [afterglow.control.devices.push-3 :as push]
            [afterglow.control.devices.session :as device]
            [clojure.test :as test :refer [deftest is]]
            [tolglow.demo :as demo]
            [tolglow.show :as show]))

(defn- model [runtime]
  (:model @(:state runtime)))

(defn- instance [runtime cue]
  (some #(when (= cue (:cue-id %)) %) (vals (:instances (model runtime)))))

(defn- queue [runtime]
  (mapv :payload (.toArray ^java.util.concurrent.LinkedBlockingQueue (:queue runtime))))

(defn- run-replay [options base run!]
  (let [time (atom 0)
        receiver (atom nil)
        runtime (show/create-runtime {:workspace-options nil :model base
                                      :physical-now-ms #(deref time)
                                      :sink {:send! (fn [_ _])}})]
    (try
      (with-redefs [show/now-ms (fn [_] @time)]
        (let [session (show/connect-device! runtime :push-3
                        (merge {:session-id "gesture-replay-543" :user-mode? true
                                :cue-gestures? true :hold-ms 100 :schedule! nil
                                :midi {:open! #(do (reset! receiver %) :virtual-midi)
                                       :close! (fn [_])}}
                               options))
              input! (fn [at bytes] (reset! time at) (@receiver bytes))
              tick! (fn [at] (reset! time at) (show/tick! runtime at))
              refresh! (fn [at] (reset! time at) (device/refresh! session))
              ;; Immediate MIDI commands wait for a receipt from the frame owner.
              sync-input! (fn [at bytes]
                            (let [enqueued (promise)
                                  submit! show/submit!]
                              (with-redefs [show/submit! (fn [& args]
                                                          (let [receipt (apply submit! args)]
                                                            (deliver enqueued true)
                                                            receipt))]
                                (let [input (future (input! at bytes))]
                                  (when-not (deref enqueued 2000 false)
                                    (future-cancel input)
                                    (throw (ex-info "MIDI command was not enqueued" {:at at :bytes bytes})))
                                  (let [submitted (queue runtime)]
                                    (tick! at)
                                    (when (= ::timeout (deref input 2000 ::timeout))
                                      (throw (ex-info "MIDI command did not receive its receipt" {:at at})))
                                    submitted)))))]
          (run! runtime session input! tick! refresh! sync-input!)
          (is (empty? (:errors (device/snapshot session))))))
      (finally (show/stop! runtime)))))

(deftest user-mode-tap-hold-and-quantized-release
  (run-replay {:expression-mode :poly-aftertouch :launch-grid {:beats 1}
               :layout {:pads {[0 0] {:channel 3 :note 12} [1 0] {:channel 3 :note 13}}
                        :buttons {:choose {:channel 5 :controller 42}}}
               :button-bindings {:choose :cue-gesture}
               :param-mappings {:level nil}}
    (assoc-in (demo/model) [:pages :main :cells] {[0 0] :ember [1 0] :ice})
    (fn [runtime session input! tick! refresh! sync-input!]
      (input! 10 [0x93 12 96])
      (input! 20 [0xa3 12 127])
      (is (empty? (queue runtime)))
      (input! 40 [0x83 12 0])
      (let [tap (first (queue runtime))]
        (is (= [:cue/launch :persistent 10 40]
               [(:op tap) (get-in tap [:launch :mode]) (get-in tap [:raw :time-ms]) (:time-ms tap)]))
        (tick! 40)
        (tick! 499)
        (is (empty? (:instances (model runtime))))
        (tick! 500)
        (is (= :running (:phase (instance runtime :ember))))
        (is (= 500 (:started-at-ms (instance runtime :ember)))))

      (input! 520 [0x93 13 96])
      (refresh! 619)
      (is (empty? (queue runtime)))
      (refresh! 620)
      (let [hold (first (queue runtime))]
        (is (= [:cue/launch :held 520 620]
               [(:op hold) (get-in hold [:launch :mode]) (get-in hold [:raw :time-ms]) (:time-ms hold)]))
        (tick! 620)
        (input! 650 [0x83 13 0])
        (let [release (first (queue runtime))]
          (is (= [:cue/cancel-launch (:command-id hold)] ((juxt :op :launch-command-id) release))))
        (tick! 650)
        (is (= :cancelled (:status (show/quantized-cue-status runtime (:command-id hold))))))

      (input! 670 [0x93 13 96])
      (refresh! 770)
      (let [hold (first (queue runtime))]
        (tick! 770)
        (tick! 999)
        (is (nil? (instance runtime :ice)))
        (tick! 1000)
        (let [receipt (show/quantized-cue-status runtime (:command-id hold))
              id (:instance-id receipt)]
          (is (= [:fired 1000 (:id (instance runtime :ice))]
                 [(:status receipt) (get-in receipt [:admitted-at :time-ms]) id]))
          (refresh! 1000)
          (is (= id (:selected-instance (push/control-view (:local (device/snapshot session)) (model runtime)))))
          (input! 1005 [0x83 13 0])
          (tick! 1005)
          (is (= :releasing (get-in (model runtime) [:instances id :phase])))
          (is (= :running (:phase (instance runtime :ember))))
          (println (pr-str {:mode :user-mode :strike (:raw receipt) :admitted (:admitted-at receipt)
                            :held-instance id :release-phase :releasing}))))

      (let [id (:id (instance runtime :ember))]
        (input! 1010 [0xb5 42 127])
        (input! 1011 [0x93 12 96])
        (input! 1012 [0x83 12 0])
        (input! 1013 [0xb5 42 0])
        (is (empty? (queue runtime)))
        (is (= id (:selected-instance (push/control-view (:local (device/snapshot session)) (model runtime)))))
        (input! 1020 [0x93 12 96])
        (let [[end] (sync-input! 1030 [0x83 12 0])]
          (is (= [:instance/end id] ((juxt :op :instance-id) end)))
          (is (= :releasing (get-in (model runtime) [:instances id :phase]))))))))

(deftest mpe-active-hold-routes-expression-by-exact-voice
  (let [position {:type :vector :bounds [-2 2] :size 3 :default [0 0 0]}
        base (-> (demo/model)
                 (assoc-in [:pages :main :cells] {[0 0] :ember [1 0] :ice})
                 (assoc-in [:registry :effects :ember :params :position] position)
                 (assoc-in [:registry :effects :ice :params :position] position))]
    (run-replay {:expression-mode :mpe :layout {} :zone {:manager-channel 0 :member-channels [1 2]}
                 :mpe-note-cells {40 [0 0] 41 [1 0]}
                 :param-mappings {:level :pressure
                                  :position [{:axis :glide :component 0} {:axis :slide :component 2}]}}
      base
      (fn [runtime _ input! tick! refresh! sync-input!]
        (let [replies (mapv #(show/submit! runtime {:op :cue/launch :cue-id %}) [:ember :ice])]
          (tick! 10)
          (is (= [:accepted :accepted] (mapv #(:status (deref % 0 nil)) replies))))
        (let [a (:id (instance runtime :ember)) b (:id (instance runtime :ice))]
          (input! 20 [0x91 40 96])
          (input! 30 [0x92 41 64])
          (input! 119 [0xd1 127])
          (input! 120 [0xe1 127 127])
          (is (empty? (queue runtime)))
          (refresh! 130)
          (let [commands (vec (concat (sync-input! 131 [0xd1 127])
                                      (sync-input! 132 [0xe1 127 127])
                                      (sync-input! 133 [0xb2 74 0])))
                edits (mapv (juxt :instance-id :param :value) commands)]
            (is (= [[a :level 1.0] [a :position [2.0 0 0]] [b :position [0 0 -2.0]]] edits))
            (is (= [2.0 0 0] (get-in (model runtime) [:instances a :params :position])))
            (is (= [0 0 -2.0] (get-in (model runtime) [:instances b :params :position])))
            (input! 134 [0x81 40 0])
            (input! 135 [0x82 41 0])
            (is (empty? (queue runtime)))
            (is (= [:running :running] (mapv (fn [id] (get-in (model runtime) [:instances id :phase])) [a b])))
            (println (pr-str {:mode :mpe :edits edits :phases-after-note-off [:running :running]}))))))))

(let [{:keys [fail error]} (test/run-tests 'push-cue-gesture-replay-543)]
  (shutdown-agents)
  (System/exit (if (zero? (+ fail error)) 0 1)))

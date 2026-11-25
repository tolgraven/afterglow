(require '[afterglow.control.devices.session :as session]
         '[clojure.data.json :as json]
         '[tolglow.demo :as demo]
         '[tolglow.show :as show])

(defn submit-at! [runtime time operation]
  (let [reply (show/submit! runtime operation)]
    (show/tick! runtime time)
    (let [result (deref reply 1000 nil)]
      (assert (= :accepted (:status result)) (pr-str result))
      result)))

(defn receive-at! [runtime receive time bytes]
  (let [result (future (receive bytes))
        deadline (+ (System/nanoTime) 6000000000)]
    (try
      (loop []
        (show/tick! runtime time)
        (when-not (realized? result)
          (assert (< (System/nanoTime) deadline) (pr-str bytes))
          (Thread/sleep 2)
          (recur)))
      @result
      (finally (future-cancel result)))))

(defn capture [mode]
  (let [effect {:type :number :default 1 :bounds [1/4 4] :semantic/type :beat-ratio
                :ratio-components {:numerator [1 9] :denominator [1 11]}}
        model (-> (demo/model)
                  (assoc-in [:registry :effects :ember :params :period] effect)
                  (assoc-in [:registry :effects :ember :param-order] [:period :level]))
        runtime (show/create-runtime {:model model :workspace-options nil})
        receive (atom nil)
        screen (atom nil)
        options (cond->
                 {:session-id (name mode) :user-mode? true :expression-mode mode
                  :cue-variations? true :schedule! nil
                  :layout {:encoder-touches {:period {:channel 2 :note 9}}
                           :encoders {:period {:channel 2 :controller 19}}}
                  :encoder-bindings {:period {:param :period}}
                  :display {:device :push-3 :input :view
                            :open! (constantly :capture-view)
                            :render! (fn [_ view] (reset! screen view))
                            :close! (fn [_])}
                  :midi {:open! #(do (reset! receive %) :virtual-midi)
                         :send! (fn [_ bytes] (throw (ex-info "Unexpected MIDI output" {:bytes bytes})))
                         :close! (fn [_])}}
                 (= mode :mpe) (assoc :zone {:manager-channel 0 :member-channels [1]}
                                      :mpe-note-cells {40 [0 0]}))]
    (try
      (let [instance-id (:instance-id (submit-at! runtime 0 {:op :cue/launch :cue-id :ember}))
            device (show/connect-device! runtime :push-3 options)
            model #(:model @(:state runtime))
            record (fn [time stage]
                     (show/tick! runtime time)
                     (session/refresh! device)
                     (let [level (get-in (model) [:instances instance-id :params :period])
                           display-value (:value (some #(when (= :period (:param %)) %) (:parameters @screen)))
                           local (:local (session/snapshot device))
                           history (get-in (model) [:control :edit-history])]
                       (assert (= instance-id (:instance-id @screen)
                                              (:selected-instance (or (:controls local) local))))
                       (assert (= level display-value) (pr-str [level display-value]))
                       {:stage stage :time-ms time :ratio (str level)
                        :display (str display-value) :exact-fraction? (ratio? level)
                        :fine? (boolean (:fine? @screen))
                        :temporary? (boolean (get-in history [:open [:instance-param instance-id :period] :temporary?]))
                        :undo (get history :cursor 0)}))
            input! #(receive-at! runtime @receive %1 %2)
            before (record 10 :preferred)
            _ (input! 20 [0xb2 19 1])
            preferred (record 21 :preferred-turn)
            _ (submit-at! runtime 30 {:op :cue-variation/ratio-mode :instance-id instance-id :mode :free})
            _ (submit-at! runtime 40 {:op :cue-variation/ratio-set :instance-id instance-id :param :period
                                       :numerator 5 :denominator 11})
            free (record 41 :free)
            _ (input! 50 [0xb0 49 127])
            _ (input! 60 [0xb0 57 127])
            _ (input! 70 [0x92 9 127])
            _ (input! 80 [0xb2 19 1])
            temporary (record 81 :accent-turn)
            _ (input! 90 [0xb0 57 0])
            held (record 91 :accent-released)
            _ (input! 100 [0x82 9 0])
            restored (record 101 :restored)]
        (assert (= ["1" "5/11" "5/11"] (mapv :ratio [before free restored])))
        (assert (every? :exact-fraction? [preferred temporary held restored]))
        (assert (= (:ratio temporary) (:ratio held)))
        (assert (not= (:ratio free) (:ratio temporary)))
        (assert (and (:fine? temporary) (:temporary? temporary) (:temporary? held)
                     (not (:temporary? restored)) (= (:undo free) (:undo restored))))
        (assert (empty? (:errors (session/snapshot device))))
        {:mode mode :rows [before preferred free temporary held restored]})
      (finally (show/stop! runtime)))))

(let [[destination tolglow afterglow] *command-line-args*]
  (spit destination (json/write-str {:tolglow tolglow :afterglow afterglow
                                    :transport "Virtual MIDI, captured display"
                                    :devices (mapv capture [:poly-aftertouch :mpe])}))
  (shutdown-agents))

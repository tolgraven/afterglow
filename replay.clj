(require '[afterglow.control.devices.session :as session]
         '[clojure.data.json :as json]
         '[clojure.java.shell :as shell]
         '[clojure.string :as str]
         '[tolglow.show :as show])

(defn require-head! [directory expected]
  (let [{:keys [exit out]} (shell/sh "git" "-C" directory "rev-parse" "HEAD")]
    (assert (and (zero? exit) (= expected (str/trim out)))
            (str "Use the recorded source head for " directory))))

(let [[output afterglow-head tolglow-head] *command-line-args*
      _ (require-head! (System/getenv "AFTERGLOW_ROOT") afterglow-head)
      _ (require-head! "." tolglow-head)
      receive (atom nil)
      view (atom nil)
      dimmer (atom nil)
      rows (atom [])
      runtime (show/create-runtime
                {:workspace-options nil
                 :sink {:send! (fn [packet _]
                                 (reset! dimmer (bit-and 255 (aget ^bytes (get packet 1) 0))))}})]
  (try
    (with-redefs [show/device-command-wait-ms 0]
      (let [launch (show/submit! runtime {:op :cue/launch :cue-id :ember})
            _ (show/tick! runtime 0)
            id (:instance-id @launch)
            device (show/connect-device!
                     runtime :push-3
                     {:session-id "push3-replay" :user-mode? true :expression-mode :poly-aftertouch
                      :layout {:encoder-touches {:level {:channel 2 :note 9}}
                               :encoders {:level {:channel 2 :controller 19}}
                               :buttons {:shift-button {:channel 4 :controller 23}}}
                      :encoder-bindings {:level {:param :level}}
                      :button-bindings {:shift-button :shift}
                      :operator-gestures? true :temporary-encoder-modifier :shift :schedule! nil
                      :midi {:open! #(do (reset! receive %) :replay-midi) :close! (fn [_])
                             :send! (fn [_ _] (throw (ex-info "Unexpected MIDI output" {})))}
                      :display {:device :push-3 :input :view :open! (constantly :replay-display)
                                :render! (fn [_ next-view] (reset! view next-view)) :close! (fn [_])}})
            input! (fn [time label bytes]
                     (when bytes (@receive bytes))
                     (show/tick! runtime time)
                     (session/refresh! device)
                     (let [model (:model @(:state runtime))
                           history (get-in model [:control :edit-history])
                           row {:time-ms time :operation label :midi bytes
                                :level (get-in model [:instances id :params :level]) :dimmer @dimmer
                                :fine (:fine? @view) :history-cursor (get history :cursor 0)
                                :open-gestures (count (:open history))}]
                       (swap! rows conj row)
                       row))]
        (assert (= id (get-in (session/snapshot device) [:local :selected-instance])))
        (let [baseline (input! 110 "Baseline" nil)
              _ (input! 120 "Hold Shift" [0xb4 23 127])
              _ (input! 130 "Touch Level encoder" [0x92 9 127])
              peak (input! 140 "Turn Level encoder" [0xb2 19 24])
              modifier-up (input! 150 "Release Shift first" [0xb4 23 0])
              last-turn (input! 160 "Keep turning" [0xb2 19 3])
              saved (show/export-show runtime)
              _ (dotimes [_ 256] (show/submit! runtime {:op :master/set :value 1}))
              full? (= :rejected (:status (deref (show/submit! runtime {:op :master/set :value 1}) 0 nil)))
              _ (@receive [0x82 9 0])
              {:keys [payload authority reply]} (first (vals @(:push-gesture-ends runtime)))
              cancelled (input! 170 "Lift Level encoder while ordinary queue is full" nil)
              _ (swap! rows update 6 assoc :midi [0x82 9 0])
              _ (input! 180 "Touch without Shift" [0x92 9 127])
              ordinary (input! 190 "Turn ordinary edit" [0xb2 19 4])
              committed (input! 200 "Lift ordinary edit" [0x82 9 0])]
          (assert (= (select-keys baseline [:level :dimmer :history-cursor])
                     (select-keys cancelled [:level :dimmer :history-cursor])))
          (assert (= (:level peak) (:level modifier-up)))
          (assert (< (:dimmer baseline) (:dimmer peak) (:dimmer last-turn)))
          (assert (= (:level baseline) (get-in saved [:model :instances id :params :level])))
          (assert (nil? (:frame-output saved)))
          (assert (= (:level ordinary) (:level committed)))
          (assert (= 1 (:history-cursor committed)))
          (assert (and full? (= :gesture/cancel (:op payload)) (= :accepted (:status @reply))))
          (assert (= {:adapter :push-3 :session-id "push3-replay"}
                     (:source payload) (::show/push-source authority)))
          (assert (empty? (:errors (session/snapshot device))))
          (spit output (json/write-str {:afterglow afterglow-head :tolglow tolglow-head
                                        :input "Synthetic MIDI capture replay"
                                        :cancel {:source (:source payload) :queue-full full? :status (:status @reply)}
                                        :saved-level (get-in saved [:model :instances id :params :level])
                                        :saved-frame (boolean (:frame-output saved)) :rows @rows})))))
    (finally (show/stop! runtime) (shutdown-agents))))

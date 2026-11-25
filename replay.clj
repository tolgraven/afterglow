(require '[afterglow.control.codecs.push-2 :as push-2-midi]
         '[afterglow.control.devices.session :as device-session]
         '[clojure.data.json :as json]
         '[clojure.test :as test]
         '[tolglow.show :as show]
         '[tolglow.studio.modulation-host-test])

(defn capture-device [kind]
  (let [receive (atom nil)
        dimmer (atom nil)
        rows (atom [])
        push-2? (= :push-2 kind)
        note (if push-2? 0 9)
        cc (if push-2? 71 19)
        channel (if push-2? 0 2)
        runtime (show/create-runtime
                 {:workspace-options nil
                  :sink {:send! (fn [packet _]
                                  (reset! dimmer (bit-and 255 (aget ^bytes (get packet 1) 0))))}})
        options (cond-> {:session-id (name kind)
                         :schedule! nil
                         :timeout-ms 30000
                         :midi {:open! #(do (reset! receive %) :virtual-midi)
                                :send! (fn [_ _])
                                :close! (fn [_])}}
                  (not push-2?)
                  (merge {:user-mode? true
                          :expression-mode :poly-aftertouch
                          :layout {:encoder-touches {:level {:channel 2 :note 9}}
                                   :encoders {:level {:channel 2 :controller 19}}}
                          :encoder-bindings {:level {:param :level}}
                          :display {:device :push-3 :input :view
                                    :open! (constantly :capture-view)
                                    :render! (fn [_ _])
                                    :close! (fn [_])}}))]
    (try
      (with-redefs [show/device-command-wait-ms 0]
        (let [launch (show/submit! runtime {:op :cue/launch :cue-id :ember})
              _ (show/tick! runtime 0)
              id (:instance-id @launch)
              device (show/connect-device! runtime kind options)
              model #(:model @(:state runtime))
              level #(get-in (model) [:instances id :params :level])
              history #(get-in (model) [:control :edit-history])
              record! (fn [time action bytes]
                        (when bytes (@receive bytes))
                        (show/tick! runtime time)
                        (let [row {:time-ms time :step action :midi bytes :level (level)
                                   :dimmer @dimmer :undo (get (history) :cursor 0)
                                   :temporary? (boolean (get-in (history) [:open [:instance-param id :level] :temporary?]))}]
                          (swap! rows conj row)
                          row))
              touch [(+ 0x90 channel) note 127]
              lift [(+ 0x80 channel) note 0]
              turn (fn [ticks] [(+ 0xb0 channel) cc ticks])]
          (assert id)
          (assert (not-any? #(contains? options %) [:operator-gestures? :temporary-encoder-modifier]))
          (when push-2?
            (doseq [index (range 128)]
              (@receive (assoc (push-2-midi/palette-write 0 index [0 0 0 0]) 6 4))))
          (let [before (record! 100 :before nil)
                _ (record! 110 :accent-down [0xb0 57 127])
                touched (record! 120 :accent-touch touch)
                preview (record! 130 :audition (turn 20))
                _ (record! 140 :accent-released [0xb0 57 0])
                still-temporary (record! 150 :audition-after-release (turn 2))
                saved (get-in (show/export-show runtime) [:model :instances id :params :level])
                restored (record! 160 :restored lift)
                _ (record! 410 :ordinary-touch touch)
                _ (record! 420 :ordinary-turn (turn 1))
                ordinary (record! 430 :ordinary-commit lift)
                _ (record! 440 :shift-down [0xb0 49 127])
                fine-touch (record! 680 :shift-touch touch)
                _ (record! 690 :shift-turn (turn 1))
                fine (record! 700 :shift-commit lift)
                _ (record! 710 :shift-released [0xb0 49 0])]
            (assert (:temporary? touched))
            (assert (:temporary? still-temporary))
            (assert (< (:dimmer before) (:dimmer preview) (:dimmer still-temporary)))
            (assert (= (select-keys before [:level :dimmer :undo])
                       (select-keys restored [:level :dimmer :undo])))
            (assert (= (:level before) saved))
            (assert (not (:temporary? fine-touch)))
            (assert (= [1 2] (mapv :undo [ordinary fine])))
            (assert (< 0 (- (:level fine) (:level ordinary)) (- (:level ordinary) (:level restored))))
            (assert (empty? (:errors (device-session/snapshot device))))
            {:device kind :saved-level saved :samples @rows})))
      (finally (show/stop! runtime)))))

(let [[output afterglow tolglow] *command-line-args*
      verification (test/run-tests 'tolglow.studio.modulation-host-test)]
  (assert (zero? (+ (:fail verification) (:error verification))))
  (spit output (json/write-str {:afterglow afterglow :tolglow tolglow
                               :capture "Virtual MIDI and in-memory DMX"
                               :devices (mapv capture-device [:push-2 :push-3])})))

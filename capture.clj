(require '[afterglow.control.codecs.push-2 :as midi]
         '[clojure.data.json :as json]
         '[tolglow.show :as show])

(let [[out afterglow-rev tolglow-rev] *command-line-args*
      callbacks (atom nil)
      dimmer (atom nil)
      rows (atom [])
      runtime (show/create-runtime {:workspace-options nil
                                    :sink {:send! (fn [packet _]
                                                    (reset! dimmer (bit-and 255 (aget ^bytes (get packet 1) 0))))}})]
  (try
    (with-redefs [show/device-command-wait-ms 0]
      (let [reply (show/submit! runtime {:op :cue/launch :cue-id :ember})
            _ (show/tick! runtime 0)
            id (:instance-id @reply)
            opts {:session-id "capture" :operator-gestures? true :temporary-encoder-modifier :shift
                  :schedule! nil :timeout-ms 30000
                  :midi {:open! #(do (reset! callbacks %) :virtual-midi)
                         :send! (fn [_ _]) :close! (fn [_])}}
            _ (show/connect-device! runtime :push-2 opts)
            model #(:model @(:state runtime))
            value #(get-in (model) [:instances id :params :level])
            start 100
            input! (fn [time title bytes]
                     (when bytes (@callbacks bytes))
                     (show/tick! runtime time)
                     (swap! rows conj {:time time :title title :midi bytes :level (value) :dimmer @dimmer
                                       :entries (get-in (model) [:control :edit-history :cursor] 0)
                                       :open (count (get-in (model) [:control :edit-history :open]))}))]
        (assert id)
        (doseq [index (range 128)]
          (@callbacks (assoc (midi/palette-write 0 index [0 0 0 0]) 6 4)))
        (input! start "Baseline" nil)
        (input! 120 "Hold Shift" [0xb0 49 127])
        (input! 130 "Touch encoder 1" [0x90 0 127])
        (input! 140 "Turn encoder 1" [0xb0 71 30])
        (input! 150 "Release Shift first" [0xb0 49 0])
        (input! 160 "Keep turning" [0xb0 71 5])
        (let [snapshot (show/export-show runtime)]
          (swap! rows update 5 assoc :saved-level (get-in snapshot [:model :instances id :params :level])
                                    :saved-frame (boolean (:frame-output snapshot))))
        (input! 170 "Lift encoder 1" [0x80 0 0])
        (input! 180 "Touch without Shift" [0x90 0 127])
        (input! 190 "Turn ordinary edit" [0xb0 71 6])
        (input! 200 "Lift ordinary edit" [0x80 0 0])
        (let [[baseline _ _ peak modifier-up last-turn cancelled _ ordinary committed] @rows]
          (assert (= (select-keys baseline [:level :dimmer :entries])
                     (select-keys cancelled [:level :dimmer :entries])))
          (assert (= (:dimmer peak) (:dimmer modifier-up)))
          (assert (< (:dimmer baseline) (:dimmer peak) (:dimmer last-turn)))
          (assert (= (:level baseline) (:saved-level last-turn)))
          (assert (false? (:saved-frame last-turn)))
          (assert (= (:dimmer ordinary) (:dimmer committed)))
          (assert (= 1 (:entries committed))))
        (spit out (json/write-str {:afterglow afterglow-rev :tolglow tolglow-rev :rows @rows}))))
    (finally (show/stop! runtime))))

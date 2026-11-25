(require '[afterglow.control.codecs.push-2 :as midi]
         '[clojure.data.json :as json]
         '[tolglow.demo :as demo]
         '[tolglow.show :as show])

(defn capture-color! [output afterglow-head tolglow-head]
  (let [original [0.82 0.20 0.11]
        model (update-in (demo/model) [:registry :effects :ember] assoc
                         :params {:tint {:type :color :default original}}
                         :param-order [:tint]
                         :outputs {:color (demo/param :tint) :dimmer (demo/constant 0.8)})
        receive (atom nil)
        dmx (atom nil)
        runtime (show/create-runtime
                  {:model model :workspace-options nil
                   :sink {:send! (fn [packet _]
                                   (let [universe ^bytes (get packet 1)]
                                     (reset! dmx (mapv #(bit-and 255 (aget universe %)) [1 2 3 4]))))}})]
    (try
      (with-redefs [show/device-command-wait-ms 0]
        (let [launch (show/submit! runtime {:op :cue/launch :cue-id :ember})
              _ (show/tick! runtime 0)
              id (:instance-id @launch)
              _ (assert id)
              _ (show/connect-device! runtime :push-2
                                      {:session-id "momentary-color" :schedule! nil
                                       :operator-gestures? true :temporary-encoder-modifier 41
                                       :midi {:open! #(do (reset! receive %) :virtual-midi)
                                              :send! (fn [_ _]) :close! (fn [_])}})
              input! (fn [time action bytes]
                       (when bytes (@receive bytes))
                       (show/tick! runtime time)
                       (let [model (:model @(:state runtime))]
                         {:time-ms time :action action :midi bytes :rgbw @dmx
                          :value (get-in model [:instances id :params :tint])
                          :history (get-in model [:control :edit-history :cursor] 0)}))]
          (doseq [index (range 128)]
            (@receive (assoc (midi/palette-write 0 index [0 0 0 0]) 6 4)))
          (let [baseline (input! 110 "Baseline" nil)
                mod-down (input! 120 "Hold modifier" [0xb0 41 127])
                touch (input! 130 "Touch color encoder" [0x90 0 127])
                yellow (input! 140 "Turn color encoder" [0xb0 71 12])
                mod-up (input! 150 "Release modifier first" [0xb0 41 0])
                green (input! 160 "Keep turning" [0xb0 71 16])
                saved-value (get-in (show/export-show runtime) [:model :instances id :params :tint])
                lift (input! 170 "Lift encoder" [0x80 0 0])]
            (assert (= original (:value baseline) (:value lift) saved-value))
            (assert (= (:rgbw baseline) (:rgbw lift)))
            (assert (= (:value yellow) (:value mod-up)))
            (assert (= 3 (count (set (map :rgbw [baseline yellow green])))))
            (assert (= 0 (:history lift)))
            (spit output (json/write-str {:afterglow afterglow-head :tolglow tolglow-head
                                          :saved-value saved-value
                                          :rows [baseline mod-down touch yellow mod-up green lift]})))))
      (finally (show/stop! runtime)))))

(apply capture-color! *command-line-args*)

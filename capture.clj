(require '[afterglow.control.codecs.push-2 :as codec]
         '[afterglow.control.devices.session :as session]
         '[clojure.data.json :as json]
         '[tolglow.demo :as demo]
         '[tolglow.show :as show])

(defn fixture-show []
  (-> (demo/model)
      (assoc-in [:registry :cues :ember :duration] {:bars 64})
      (assoc-in [:registry :effects :ember :params :period]
                {:type :number :default 1 :bounds [1/4 4] :semantic/type :beat-ratio
                 :ratio-components {:numerator [1 9] :denominator [1 11]}})
      (assoc-in [:registry :effects :ember :params :tint]
                {:type :color :default [0.9 0.4 0.15]})
      (assoc-in [:registry :effects :ember :param-order] [:period :level :tint])
      (assoc-in [:registry :effects :ember :outputs :color] {:op :param :key :tint})))

(defn recorder []
  (let [receive (atom nil) pending? (atom false) sent (atom []) views (atom [])
        ack (codec/sysex 0 [0x09])]
    {:midi {:open! #(do (reset! receive %) :capture)
            :send! (fn [_ batch]
                     (swap! sent into batch)
                     (when (= ack (peek batch)) (reset! pending? true)))
            :close! (fn [_])}
     :display {:open! (constantly :capture) :render! (fn [_ view] (swap! views conj view)) :close! (fn [_])}
     :receive! #(@receive %)
     :messages sent :views views
     :setup! (fn []
               (doseq [index (range 128)]
                 (@receive (assoc (codec/palette-write 0 index [0 0 0 73]) 6 4))))
     :settle! (fn []
                (loop [remaining 10]
                  (when (compare-and-set! pending? true false)
                    (assert (pos? remaining) "Push palette did not settle")
                    (@receive ack)
                    (recur (dec remaining)))))}))

(defn elapsed-ms [since]
  (quot (- (System/nanoTime) since) 1000000))

(defn wait-until! [since target]
  (let [remaining (- target (elapsed-ms since))]
    (when (pos? remaining) (Thread/sleep remaining))))

(defn snapshot [runtime device recorder since event]
  (let [{:keys [model output]} @(:state runtime)
        {:keys [local last-ack]} (session/snapshot device)
        {:keys [id params system]} (get-in model [:instances (:selected-instance local)])
        presented (:pad-overlay-presented local)
        cells (into {} (map (juxt :position :kind)) (:cells presented))
        frame (get-in output [:universes 1])]
    {:capture-ms (elapsed-ms since) :show-time-ms (:time-ms model) :show-revision (:revision model)
     :frame-number (:frame-number model) :instance-id id :cue-id (:cue-id presented)
     :layout (:layout presented) :params (update params :period str) :opacity (:opacity system)
     :dimmer-byte (when frame (bit-and 255 (aget ^bytes frame 0)))
     :event event :ack (select-keys last-ack [:status :command-id :slot :instance-id :revision])
     :midi-message-count (count @(:messages recorder))
     :pads (mapv (fn [[xy rgb]] {:x (first xy) :y (second xy) :rgb rgb :kind (get cells xy)})
                 (sort-by key (:last-leds local)))}))

(defn run-capture! [destination]
  (let [runtime (show/start! {:model (fixture-show) :workspace-options nil :frame-rate 30 :recovery false}
                             (constantly nil))
        capture (recorder)
        {:keys [receive! setup! settle!]} capture]
    (try
      (let [device (show/connect-device! runtime :push-2
                     (merge {:session-id "video-capture" :schedule! nil :timeout-ms 60000
                             :cue-variations? true}
                            (select-keys capture [:midi :display])))
            button! (fn [cc] (receive! [0xb0 cc 127]) (receive! [0xb0 cc 0]))
            pad! (fn [[x y]]
                   (let [note (codec/pad-note x y)]
                     (receive! [0x90 note 100])
                     (receive! [0x80 note 0])))
            presented #(get-in (session/snapshot device) [:local :pad-overlay-presented])
            params #(get-in @(:state runtime) [:model :instances (:instance-id (presented)) :params])]
        (setup!)
        (settle!)
        (pad! [0 0])
        (settle!)
        (button! 50)
        (settle!)
        (assert (= :full (:layout (presented))))
        (let [initial (params)
              ms 7600
              events {850 (fn []
                            (receive! [0xb0 86 127])
                            (button! 50)
                            (receive! [0xb0 86 0])
                            (settle!)
                            (assert (= initial (:params (first (:cells (presented))))))
                            {:id :saved :label "Saved current state in slot 1" :pad [0 0]})
                      2500 (fn []
                             (let [{:keys [position params]}
                                   (apply max-key #(Math/abs (- (get-in % [:params :level]) (:level initial)))
                                          (filter #(= :generated (:kind %)) (:cells (presented))))]
                               (pad! position)
                               (settle!)
                               (assert (= params (get-in @(:state runtime)
                                                         [:model :instances (:instance-id (presented)) :params])))
                               (assert (not= params initial))
                               {:id :generated :label "Applied a generated full state" :pad position}))
                      4880 (fn []
                             (pad! [0 0])
                             (settle!)
                             (assert (= initial (params)))
                             {:id :recalled :label "Recalled saved slot 1" :pad [0 0]})}
              start (System/nanoTime)
              frames (loop [pending (sort-by key events) frame-time 0
                            event {:id :ready :label "Full-state overlay ready"} frames []]
                       (if (> frame-time ms)
                         frames
                         (do (wait-until! start frame-time)
                             (let [[at perform] (first pending)
                                   trigger? (and at (>= frame-time at))
                                   event (if trigger? (perform) event)]
                               (recur (if trigger? (next pending) pending) (+ frame-time 80) event
                                      (conj frames (snapshot runtime device capture start event)))))))]
          (assert (empty? (:errors (session/snapshot device))))
          (assert (= [:ready :saved :generated :recalled] (vec (distinct (map (comp :id :event) frames)))))
          (spit destination (json/write-str {:duration-ms ms :frames frames
                                             :transport "captured Push 2 MIDI and acknowledged LED state"
                                             :tolglow-sha "5ae037b53de115e178362ab1bb85915a368d5dbb"
                                             :afterglow-sha "811ee88f0d2ac4143ab495ca0d1449601acb857d"}))
          (println "Captured" (count frames) "committed observations for" (pr-str (distinct (map (comp :id :event) frames))))))
      (finally (show/stop! runtime) (shutdown-agents)))))

(run-capture! (first *command-line-args*))

(require '[afterglow.control.devices.push-3.display :as push-screen]
         '[afterglow.control.devices.session :as session]
         '[clojure.data.json :as json]
         '[clojure.java.io :as io]
         '[tolglow.demo :as demo]
         '[tolglow.show :as show]
         '[tolglow.studio :as studio]
         '[tolglow.studio.display :as display])
(import '[java.nio.file Files] '[java.util Arrays] '[javax.imageio ImageIO])

(defn demo-show []
  (-> (demo/model)
      (assoc-in [:pages :main :cells [7 0]] :ember)
      (assoc-in [:registry :cues :ember :duration] {:bars 64})
      (assoc-in [:registry :effects :ember :envelope] {:attack {:beats 0} :release {:beats 128}})
      (assoc-in [:registry :effects :ember :params :period]
                {:type :number :default 1 :bounds [1/4 4] :semantic/type :beat-ratio
                 :ratio-components {:numerator [1 9] :denominator [1 11]}})
      (assoc-in [:registry :effects :ember :param-order] [:period :level])))

(defn wait-for [label operation]
  (let [deadline (+ (System/nanoTime) 45000000000)]
    (loop []
      (or (operation)
          (if (< (System/nanoTime) deadline)
            (do (Thread/sleep 25) (recur))
            (throw (ex-info "Replay step timed out" {:step label})))))))

(defn capture-wire []
  (let [wire (atom nil)
        stage (atom nil)
        presented (atom nil)
        tick (atom nil)
        native (push-screen/sink
                 {:backend {:open! (constantly :recorded-wire) :close! (fn [_])
                            :write! (fn [_ ^bytes bytes]
                                      (if (= 16 (alength bytes))
                                        (reset! wire {:header (aclone bytes)})
                                        (do (assert (= 327680 (alength bytes)))
                                            (assert (:header @wire))
                                            (swap! wire assoc :payload (aclone bytes)))))}
                  :schedule! #(do (reset! tick %) (fn []))})
        sink (assoc native
               :render-with-receipt!
               (fn [handle {:keys [image view]} receipt]
                 ((:render-with-receipt! native) handle image
                  (fn []
                    (receipt)
                    (reset! presented (assoc @wire :time-ns (System/nanoTime)
                                                  :image image :view view))))
                 (reset! stage view)))]
    {:sink sink :stage stage :presented presented :tick #(when-let [transfer @tick] (transfer))}))

(defn model [runtime] (:model @(:state runtime)))

(defn save-frame! [dir label {:keys [header payload image view time-ns]} state]
  (let [header-path (str "frames/" label ".header")
        payload-path (str "frames/" label ".bgr565")
        source-path (str "frames/" label "-chromium.png")]
    (assert (= 16 (alength ^bytes header)))
    (assert (Arrays/equals ^bytes header
                          ^bytes (byte-array (map unchecked-byte [255 204 170 136 0 0 0 0 0 0 0 0 0 0 0 0]))))
    (assert (= 327680 (alength ^bytes payload)))
    (Files/write (.toPath (io/file dir header-path)) ^bytes header (make-array java.nio.file.OpenOption 0))
    (Files/write (.toPath (io/file dir payload-path)) ^bytes payload (make-array java.nio.file.OpenOption 0))
    (ImageIO/write image "png" (io/file dir source-path))
    (println label (get-in state [:ack :status]) (:params state) (:dimmer-byte state))
    (assoc state :label label :header header-path :payload payload-path :source source-path :time-ns time-ns
                 :display-mode (:display-mode view) :overlay (:pad-overlay view))))

(defn run-replay! [dir chromium playwright runtime origin]
  (let [{:keys [sink stage presented tick]} (capture-wire)
        midi (atom nil)
        actual-capture display/process-capture
        pads (into {} (for [y (range 8) x (range 8)]
                        [[x y] {:channel 3 :note (+ 16 x (* y 8))}]))
        button-ids {:cycle 28 :record 29}
        options {:session-id "push3-physical-values-injected-wire" :schedule! nil
                 :user-mode? true :expression-mode :poly-aftertouch :launch-mode :held
                 :cue-variation-pads? true
                 :layout {:pads pads
                          :buttons (into {} (map (fn [[id cc]] [id {:channel 4 :controller cc}])) button-ids)}
                 :button-bindings {:cycle :variation/cycle :record :variation/record}
                 :midi {:open! #(do (reset! midi %) :injected-midi)
                        :send! (fn [_ _] (throw (ex-info "Unexpected outbound Push MIDI" {})))
                        :close! (fn [_])}}
        browser-options {:device :push-3 :presentation-receipts? true :sink sink
                         :url (str origin "/push-display") :browser-executable chromium :playwright-module playwright
                         :no-sandbox? true :startup-timeout-ms 60000 :capture-timeout-ms 30000
                         :max-fps 10 :shutdown-timeout-ms 5000}
        device (with-redefs [display/process-capture
                             (fn [options]
                               (update (actual-capture options) :capture!
                                       (fn [take-frame]
                                         (fn [handle view] {:view view :image (take-frame handle view)}))))]
                 (show/connect-device! runtime :push-3
                                       (assoc options :display (show/push-browser-display runtime browser-options))))
        local #(-> device session/snapshot :local)
        id (atom nil)
        current #(get-in (model runtime) [:instances @id])
        ack #(get (session/snapshot device) :last-ack)
        check-ack (fn []
                    (let [receipt (ack)]
                      (assert (= :accepted (:status receipt)) (pr-str receipt))
                      receipt))
        read-state (fn [operation receipt]
                     (let [{:keys [model output]} @(:state runtime)
                           frame (get-in output [:universes 1])]
                       {:operation operation :ack (when receipt (select-keys receipt [:status :command-id :instance-id :revision :slot]))
                        :params (some-> (current) :params (update :period str))
                        :show-revision (:revision model) :phase (:phase (current))
                        :dimmer-byte (when frame (bit-and 255 (aget ^bytes frame 0)))}))
        cc! (fn [control down?] (@midi [0xb4 (button-ids control) (if down? 127 0)]))
        cycle! (fn [] (cc! :cycle true) (cc! :cycle false))
        note! (fn [xy down?] (@midi [(if down? 0x93 0x83) (get-in pads [xy :note]) (if down? 110 0)]))
        pad! (fn [xy] (note! xy true) (note! xy false))
        await-frame! (fn [label matches?]
                       (wait-for label
                         (fn []
                           (tick)
                           (when-let [frame @presented]
                             (when (matches? (:view frame))
                               (session/refresh! device)
                               frame)))))
        basis (fn [view] (get-in (meta view) [:afterglow.control.devices.push-3/overlay-frame :projection :basis]))
        projection (fn [layout] (show/cue-variation-preview runtime {:instance-id @id :layout layout}))
        when-overlay (fn [layout projection]
                       (fn [view] (and (= layout (get-in view [:pad-overlay :layout]))
                                       (= (:basis projection) (basis view)))))
        shot! (fn [label matches? operation receipt]
                (save-frame! dir label (await-frame! label matches?) (read-state operation receipt)))]
    (try
      (let [held [7 0]
            _ (note! held true)
            launch (check-ack)
            _ (reset! id (:instance-id launch))
            _ (assert (= :held (:launch-mode (current))))
            current-params (:params (current))
            live (shot! "01-live" #(and (= @id (:instance-id %)) (nil? (:pad-overlay %))) :cue/launch launch)
            full (projection :full)
            generated (apply max-key #(Math/abs (- (double (get-in % [:params :level])) (double (:level current-params))))
                             (filter #(= :generated (:kind %)) (:cells full)))
            choice (:position generated)
            _ (cycle!)
            _ (wait-for :packed-before-transfer #(when ((when-overlay :full full) @stage) true))
            _ (pad! choice)
            _ (assert (= launch (ack)))
            _ (assert (= current-params (:params (current))))
            opened (shot! "02-open" (when-overlay :full full) :open-after-transfer nil)
            blocked {:position choice :unchanged-receipt (:command-id launch) :unchanged-params true}
            _ (cc! :record true)
            _ (cycle!)
            append (check-ack)
            _ (cc! :record false)
            saved (shot! "03-saved" (when-overlay :full (projection :full)) :cue-variation/append append)
            _ (assert (= current-params (:params (first (:cells (projection :full))))))
            _ (pad! choice)
            apply-result (check-ack)
            _ (assert (= (:params generated) (:params (current))))
            applied (shot! "04-applied" (when-overlay :full (projection :full)) :cue-variation/apply apply-result)
            _ (cycle!)
            rows (shot! "05-rows" (when-overlay :rows (projection :rows)) :open-rows nil)
            _ (pad! [0 0])
            recall (check-ack)
            _ (assert (= current-params (:params (current))))
            recalled (shot! "06-recalled" (when-overlay :rows (projection :rows)) :cue-variation/apply recall)
            _ (note! held false)
            release (check-ack)
            _ (assert (= @id (:instance-id release)))
            release-state (read-state :instance/end release)
            _ (assert (= :releasing (:phase release-state)))
            released (save-frame! dir "07-released"
                                  (await-frame! :releasing #(and (= @id (:instance-id %))
                                                                  (get-in % [:cue :releasing?])
                                                                  (nil? (:pad-overlay %))))
                                  release-state)
            frames [live opened saved applied rows recalled released]
            start (:time-ns live)]
        (assert (empty? (:errors (session/snapshot device))))
        (assert (apply distinct? (keep #(get-in % [:ack :command-id]) frames)))
        (assert (= :releasing (:phase released)))
        {:transport "Virtual Push 3 User Mode with injected MIDI input and injected USB transfers"
         :size [960 160] :packed-stride 2048 :injected true :wire-format "BGR565 little-endian"
         :held-pad held :generated-pad choice :blocked-before-transfer blocked
         :frames (mapv #(-> % (assoc :capture-ms (quot (- (:time-ns %) start) 1000000))
                             (dissoc :time-ns)) frames)})
      (finally (show/disconnect-device! runtime (:session-id options))))))

(let [[directory chromium playwright tolglow-sha afterglow-sha] *command-line-args*
      dir (io/file directory)
      _ (.mkdirs (io/file dir "frames"))
      runtime (show/start! {:model (demo-show) :workspace-options nil :workers 1
                            :frame-rate 30 :recovery false}
                           (constantly nil))]
  (try
    (let [{:keys [port stop!]} (studio/listen! runtime {:port 0})]
      (try
        (let [receipt (run-replay! dir chromium playwright runtime (str "http://127.0.0.1:" port))]
          (spit (io/file dir "receipts.json")
                (json/write-str (assoc receipt :tolglow tolglow-sha :afterglow afterglow-sha)
                                :indent true)))
        (finally (stop!))))
    (finally (show/stop! runtime) (shutdown-agents))))

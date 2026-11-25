(require '[afterglow.output.artnet :as artnet]
         '[afterglow.output.scheduler :as scheduler]
         '[afterglow.render.frame :as render]
         '[clojure.data.json :as json])

(def patch (render/compile-patch [{:id :pixel :universe 1 :address 1
                                  :channels {:red 1 :green 2 :blue 3}}]))

(defn as-bytes [^bytes packet start stop]
  (mapv #(bit-and 255 (aget packet %)) (range start stop)))

(defn trace [scenario]
  (let [clock (atom 0.0)
        callback (atom nil)
        events (atom [])
        log! (fn [type data] (swap! events conj (assoc data :event type :at-ms @clock)))
        first-send? (atom true)
        sequence-number (atom 0)
        owner (scheduler/create
               {:now-ms #(deref clock)
                :prepare-output (fn [buffers {:keys [frame-id]}]
                                  (when (and (= scenario :packing-expired) (= frame-id 1))
                                    (reset! clock 50.0))
                                  buffers)
                :send! (fn [universes id]
                         (let [packet (artnet/artdmx-packet 1 (swap! sequence-number inc) (get universes 1))
                               first? (compare-and-set! first-send? true false)]
                           (assert (= 530 (alength ^bytes packet)))
                           (assert (= [0 0 2 0] (as-bytes packet 14 18)))
                           (log! :artdmx {:frame-id id :bytes (alength ^bytes packet)
                                          :rgb (as-bytes packet 18 21)})
                           (if (and first? (= scenario :failed))
                             (do (reset! clock 49.9)
                                 (throw (ex-info "Injected sink failure following one encoded packet" {})))
                             (swap! clock + 1.0))))})
        at! (fn [_ _ due f] (reset! callback [due f]))
        offer! (fn [slot ready red]
                 (reset! clock ready)
                 (let [ticket {:slot slot :deadline-ms (* 25 slot) :started-at-ms (- ready 2)
                               :inputs-at-ms (- ready 2)}
                       token (scheduler/begin-frame! owner 1 patch {} false ticket)
                       data (byte-array 512)]
                   (aset-byte data 0 (unchecked-byte red))
                   (log! :completion {:slot slot :deadline-ms (:deadline-ms ticket) :red red
                                      :accepted (scheduler/complete! owner token {:universes {1 data}})})))
        wake! (fn [wake]
                (when (< wake @clock) (throw (ex-info "Replay clock must be monotonic" {:wake wake :now @clock})))
                (reset! clock wake)
                (let [[scheduled f] @callback]
                  (log! :wake {:scheduled-ms scheduled})
                  (f)
                  (let [status (scheduler/status owner)]
                    (log! :status (-> (select-keys status [:published :skipped-output-slots
                                                           :expired-at-publication :expired-before-send
                                                           :missed-render-deadlines :failed-publications])
                                      (assoc :due-next-ms (first @callback)
                                             :timing (:output-timing status)))))))]
    (try
      (with-redefs [scheduler/at! at!]
        (scheduler/start! owner 25)
        (offer! 1 20.0 90)
        (wake! (if (= scenario :failed) 25.0 44.0))
        (offer! 2 (if (#{:failed :packing-expired} scenario) (if (= :failed scenario) 49.95 50.0) 47.0) 180)
        (case scenario
          :recover (when (< (first @callback) 75.0)
                     (wake! 50.0)
                     (wake! (first @callback)))
          :oversleep (offer! 3 72.0 210)
          nil)
        (wake! 75.0)
        (when (= scenario :recover)
          (offer! 3 76.0 241)
          (wake! 100.0)))
      {:scenario scenario :events @events}
      (finally (scheduler/close! owner)))))

(json/pprint (mapv trace [:recover :oversleep :failed :packing-expired]))

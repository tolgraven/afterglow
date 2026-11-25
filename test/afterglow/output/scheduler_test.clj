(ns afterglow.output.scheduler-test
  (:require [clojure.test :refer [deftest is]]
            [afterglow.render.frame :as render]
            [afterglow.render.presentation :as presentation]
            [afterglow.output.retirement :as retirement]
            [afterglow.output.scheduler :as scheduler]))

(def fixtures [{:id :pixel :universe 0 :address 1 :channels {:red 1 :green 2 :blue 3}}])
(def patch (delay (render/compile-patch fixtures)))
(defn- bytes-copy [universes]
  (into {} (map (fn [[u data]] [u (mapv #(bit-and (int %) 255) data)])) universes))
(defn- capture [physical sent]
  (scheduler/create {:now-ms #(deref physical)
                     :send! (fn [universes id] (swap! sent conj {:id id :bytes (bytes-copy universes)}))}))
(defn- frame [r g b]
  {:universes {0 (byte-array (concat (map unchecked-byte [r g b]) (repeat 509 0)))}})

(deftest buffered-tracking-cuts-keep-rejected-emission-dark-between-exact-endpoints
  (let [floor {:id :floor :point [0 0 0] :normal [0 1 0] :size [20 20]}
        head (fn [id x address channels]
               {:id id :position [x 3 0] :beam-angle 20 :lens-radius-m 0.1 :universe 1
                :address address :channels (merge {:pan [1 2] :tilt [3 4]} channels)})
        patch (render/compile-patch
                [(head :lead 0 1 {:red 5}) (head :first 1 12 {:red 5})
                 (head :second 2 503 {:red {:offset 5 :presentation :hold}
                                      :dimmer {:offset 10 :fine-offset 11 :inverted-from 0 :presentation :hold}})
                 (head :downstream 3 34 {:amber 5})
                 {:id :wash :universe 1 :address 100 :channels {:dimmer 1}}])
        first-link {:leader :lead :follower :first :surface floor :along [1 0 0]}
        second-link (assoc first-link :follower :second)
        downstream (assoc first-link :leader :second :follower :downstream)
        assign (fn [id attribute value] {:target-id id :attribute attribute :value value})
        options {:mode :buffered-interpolation :period-ms 25 :latency-ms 50}
        run (fn [rich?]
              (let [clock (atom 0) sent (atom []) owner (capture clock sent)]
                (try
                  (let [frames (mapv (fn [[time red wash conflict?]]
                                       (reset! clock time)
                                       (let [rows [(assign :lead :aim [0 0 0])
                                                   (assign :lead :red 1.0) (assign :first :red 1.0)
                                                   (assign :second :aim [4.0 0 0]) (assign :second :red red)
                                                   (assign :second :dimmer 1.0) (assign :downstream :amber 1.0)
                                                   (assign :wash :dimmer wash)]
                                             links (if conflict? [first-link second-link downstream] [first-link downstream])
                                             token (scheduler/begin-frame! owner 0 patch options false)
                                             out (render/resolve-frame patch rows {:edge-tracking links :include-values? rich?
                                                                                   :compact-values? (not rich?)})]
                                         (is (true? (scheduler/complete! owner token out)))
                                         out))
                                     [[0 1.0 0.0 false] [25 0.5 0.4 true] [50 0.25 1.0 false]])]
                    (is (= [[nil nil] [nil :overlap :leader-suppressed] [nil nil]]
                           (mapv #(mapv :reason (:edge-tracking %)) frames)))
                    (doseq [at [50 62.5 75 87.5 100]]
                      (reset! clock at)
                      (scheduler/publish! owner))
                    (is (= (mapv #(bytes-copy (:universes %)) frames)
                           (mapv #(get-in @sent [% :bytes]) [0 2 4])))
                    (mapv :bytes @sent))
                  (finally (scheduler/close! owner)))))]
    (let [rich (run true) compact (run false)
          lanes (fn [universes] (mapv #(get-in universes %) [[1 506] [1 511] [2 0] [1 37] [1 99]]))]
      (is (= rich compact))
      (is (= [[255 0 0 255 0]
              [128 255 255 0 51]
              [128 255 255 0 102]
              [128 255 255 0 179]
              [64 0 0 255 255]]
             (mapv lanes rich))))))

(deftest deadline-fallback-is-independent-from-completion-and-preserves-original-time
  (let [physical (atom 0) sent (atom []) owner (capture physical sent)
        token (scheduler/begin-frame! owner 0 @patch {:mode :hold-fade} false)
        output (frame 200 100 50)]
    (try
      (scheduler/complete! owner token output)
      ;; Mutation by a renderer reusing its private output cannot leak through.
      (aset-byte ^bytes (get-in output [:universes 0]) 0 (byte 0))
      (scheduler/publish! owner)
      (is (= [200 100 50] (subvec (get-in (last @sent) [:bytes 0]) 0 3)))
      (reset! physical 25)
      (let [late (scheduler/begin-frame! owner 0 @patch {:mode :hold-fade} false)]
        (reset! physical 75)
        (scheduler/publish! owner)
        (is (= [100 50 25] (subvec (get-in (last @sent) [:bytes 0]) 0 3)))
        (reset! physical 100)
        (scheduler/complete! owner late (frame 100 80 40))
        (scheduler/publish! owner)
        (is (= [25 nil] (get-in (scheduler/status owner) [:last :source-times])))
        (is (= [50 40 20] (subvec (get-in (last @sent) [:bytes 0]) 0 3))))
      (finally (scheduler/close! owner)))))

(deftest epochs-blackout-and-close-fence-buffered-bright-output
  (let [physical (atom 0) sent (atom []) owner (capture physical sent)
        token (scheduler/begin-frame! owner 0 @patch {} false)]
    (scheduler/complete! owner token (frame 255 100 10))
    (scheduler/publish! owner)
    (reset! physical 25)
    (let [new-token (scheduler/begin-frame! owner 1 @patch {} false)]
      (is (nil? (scheduler/complete! owner token (frame 255 255 255))))
      (scheduler/publish! owner)
      (is (every? zero? (get-in (last @sent) [:bytes 0])))
      (scheduler/complete! owner new-token (frame 40 80 120))
      (scheduler/publish! owner)
      (is (= [40 80 120] (subvec (get-in (last @sent) [:bytes 0]) 0 3)))
      (reset! physical 50)
      (scheduler/begin-frame! owner 1 @patch {} true)
      (scheduler/publish! owner)
      (is (every? zero? (get-in (last @sent) [:bytes 0])))
      (scheduler/close! owner)
      (let [n (count @sent)]
        (is (nil? (scheduler/complete! owner new-token (frame 255 255 255))))
        (scheduler/publish! owner)
        (is (= n (count @sent)))))))

(deftest pending-completions-are-bounded-and-coalesce-oldest
  (let [physical (atom 0) sent (atom []) owner (capture physical sent)]
    (try
      (dotimes [n 12]
        (reset! physical n)
        (scheduler/complete! owner (scheduler/begin-frame! owner 0 @patch {} false) (frame n 0 0)))
      (is (= 3 (:pending (scheduler/status owner))))
      (is (= 9 (:coalesced (scheduler/status owner))))
      (scheduler/publish! owner)
      (is (= 11 (get-in (last @sent) [:bytes 0 0])))
      (finally (scheduler/close! owner)))))

(deftest waiting-and-blackout-present-the-configured-fog-off
  (let [sent (atom []) now (atom 0)
        nozzle {:id :fog :universe 3 :address 512 :channels {:fog {:offset 1 :fine-offset 2 :inverted-from 32}}
                :fogger {:flow-m3-min 60 :dmx-range [196.5 5]}}
        owner (scheduler/create {:now-ms #(deref now)
                                 :send! (fn [buffers _] (swap! sent conj
                                                              (mapv #(bit-and 255 (get-in buffers %)) [[3 511] [4 0]])))})
        patch (render/compile-patch [nozzle])
        token (scheduler/begin-frame! owner 0 patch {} false)]
    (scheduler/publish! owner)
    (scheduler/complete! owner token (render/resolve-frame patch [{:target-id :fog :attribute :fog :value 1.0}]))
    (scheduler/publish! owner)
    (scheduler/begin-frame! owner 0 patch {} true)
    (scheduler/publish! owner)
    (is (= [[196 128] [32 0] [196 128]] @sent))
    (scheduler/close! owner)))

(deftest idle-blackout-and-reopen-use-physical-emission-darkness
  (let [patch (render/compile-patch
                [{:id :head :universe 3 :address 503
                  :channels {:dimmer {:offset 1 :inverted-from 0}
                             :red {:offset 2 :inverted-from 0}
                             :blue {:offset 3 :inverted-from 32}
                             :pan {:offset 4 :inverted-from 0}
                             :fan {:offset 5 :inverted-from 0}
                             :amber {:offset 10 :fine-offset 11 :inverted-from 0}
                             :uv {:offset 12 :fine-offset 523 :inverted-from 2.5}
                             :white {:offset 14 :fine-offset 15 :inverted-from 0 :functions {:white [0 255]}}}}
                 {:id :lamp :universe 5 :address 512
                  :channels {:dimmer {:offset 1 :fine-offset 2 :inverted-from 0}
                             :fan {:offset 3 :inverted-from 0}}}
                 {:id :partial :universe 5 :address 8
                  :channels {:dimmer {:offset 1 :inverted-from 32}}}])
        emission-slots [[3 502] [3 503] [3 504] [3 511] [4 0] [4 1] [5 0] [4 3] [4 4] [5 511] [6 0] [5 7]]
        mechanical-slots [[3 505] [3 506] [6 1]]
        dark [255 255 0 255 255 0 0 255 0 255 255 0]
        select-bytes (fn [packet slots] (mapv #(get-in packet %) slots))
        physical (atom 0) sent (atom []) owner (capture physical sent)
        begin! (fn [dark?] (scheduler/begin-frame! owner 0 patch {} dark?))
        sent-bytes (fn [slots] (select-bytes (:bytes (peek @sent)) slots))
        assignments [{:target-id :head :attribute :dimmer :value 1.0}
                     {:target-id :head :attribute :red :value 1.0}
                     {:target-id :head :attribute :pan :value 0.25}
                     {:target-id :head :attribute :fan :value 0.5}
                     {:target-id :lamp :attribute :fan :value 0.5}
                     {:target-id :lamp :attribute :dimmer :value 1.0}]
        live (render/resolve-frame patch assignments)]
    (try
      (let [shutdown (render/idle-universes patch)
            bytes (bytes-copy shutdown)]
        (is (= dark (select-bytes bytes emission-slots)))
        (is (= [0 0 0] (select-bytes bytes mechanical-slots)))
        (aset-byte ^bytes (shutdown 3) 502 (byte 23))
        (is (= bytes (bytes-copy (render/idle-universes patch)))))
      (doseq [options [{:include-values? true} {:include-values? false :compact-values? true}]]
        (let [blackout (render/resolve-frame patch assignments (assoc options :blackout? true))
              bytes (bytes-copy (:universes blackout))]
          (is (= dark (select-bytes bytes emission-slots)))
          (is (= [191 128 128] (select-bytes bytes mechanical-slots)))))
      (let [first-token (begin! false)]
        (is (get-in (scheduler/publish! owner) [:presentation :waiting?]))
        (is (= dark (sent-bytes emission-slots)))
        (is (true? (scheduler/complete! owner first-token live)))
        (scheduler/publish! owner)
        (is (= (bytes-copy (:universes live)) (:bytes (peek @sent))))
        (reset! physical 25)
        (begin! true)
        (is (get-in (scheduler/publish! owner) [:presentation :blackout?]))
        (is (= dark (sent-bytes emission-slots)))
        (is (= [0 0 0] (sent-bytes mechanical-slots)))
        (reset! physical 50)
        (let [reopened (begin! false)]
          (is (nil? (scheduler/complete! owner first-token live)))
          (is (get-in (scheduler/publish! owner) [:presentation :waiting?]))
          (is (= dark (sent-bytes emission-slots)))
          (is (true? (scheduler/complete! owner reopened live)))
          (scheduler/publish! owner)
          (is (= (bytes-copy (:universes live)) (:bytes (peek @sent))))))
      (finally (scheduler/close! owner)))))


(deftest retired-pumps-hold-off-until-a-new-fixture-claims-the-slot
  (let [fog {:id :fog :universe 3 :address 512 :channels {:fog [1 2]}
             :fogger {:flow-m3-min 60 :dmx-range [196.5 0]}}
        old (render/compile-patch [fog])
        survivor {:id :light :universe 3 :address 7 :channels {:dimmer 1}}
        next (render/compile-patch [survivor])
        plan (retirement/plan nil old next)
        raw (render/idle-universes next)
        delivery #(retirement/include-retired plan raw)
        physical #(bit-and 255 (get-in %1 %2))]
    (is (= 196 (physical (delivery) [3 511])))
    (is (= 128 (physical (delivery) [4 0])))
    (is (not (contains? (retirement/include-retired plan {}) 3))
        "A partial transport packet cannot fabricate zeroes in the active universe.")
    (is (zero? (physical raw [3 511])) "Rendering keeps the original array.")
    (aset-byte ^bytes (get (delivery) 4) 0 (byte 2))
    (is (= 128 (physical (delivery) [4 0])) "The next packet owns its bytes.")
    (let [claimed (render/compile-patch [(assoc survivor :address 511 :footprint 3)])
          plan (retirement/plan plan next claimed)
          packet (retirement/include-retired plan (render/idle-universes claimed))]
      (is (zero? (physical packet [3 511])))
      (is (zero? (physical packet [4 0]))))))

(deftest retired-inverted-light-stays-off-until-addresses-are-reused
  (let [lamp {:id :lamp :universe 3 :address 512
              :channels {:dimmer {:offset 1 :fine-offset 2 :inverted-from 0}}}
        survivor {:id :survivor :universe 3 :address 7 :channels {:dimmer 1}}
        old (render/compile-patch [lamp survivor])
        next (render/compile-patch [survivor])
        plan (retirement/plan nil old next)
        raw (:universes (render/resolve-frame next [{:target-id :survivor :attribute :dimmer :value 0.25}]))
        delivery (fn [] (retirement/include-retired plan raw))
        lanes (fn [universes]
                (let [bytes (bytes-copy universes)]
                  (mapv #(get-in bytes %) [[3 6] [3 511] [4 0]])))]
    (is (= [64 255 255] (lanes (delivery))))
    (is (= [64 0 nil] (lanes raw)))
    (let [packet (delivery)]
      (aset-byte ^bytes (get packet 3) 511 (byte 23))
      (aset-byte ^bytes (get packet 4) 0 (byte 23))
      (is (= [64 255 255] (lanes (delivery)))))
    (let [fixture {:id :replacement :universe 3 :address 511 :footprint 3 :channels {:pan 1}}
          patched (render/compile-patch [survivor fixture])
          retired (retirement/plan plan next patched)]
      (is (= [0 0 0] (lanes (retirement/include-retired retired (render/idle-universes patched))))))
    (let [patched (render/compile-patch [survivor (assoc lamp :id :replacement :channels {:dimmer 1})])
          retired (retirement/plan plan next patched)
          active (:universes (render/resolve-frame patched [{:target-id :replacement :attribute :dimmer :value 0.5}]))]
      (is (= [0 128 255] (lanes (retirement/include-retired retired active)))))
    (let [patched (render/compile-patch [survivor (assoc lamp :id :replacement :channels {:dimmer [1 2]})])
          retired (retirement/plan plan next patched)
          active (:universes (render/resolve-frame patched [{:target-id :replacement :attribute :dimmer :value 0.5}]))]
      (is (= [0 128 0] (lanes (retirement/include-retired retired active)))))))

(deftest gate-transition-waits-for-a-sending-frame-and-fences-its-completion
  (let [sending (promise) release (promise) changing (promise) output (atom [])
        owner (scheduler/create {:now-ms (constantly 0)
                                 :send! (fn [universes _]
                                          (deliver sending true)
                                          (deref release 5000 false)
                                          (swap! output conj (get-in (bytes-copy universes) [0 0])))})
        token (scheduler/begin-frame! owner 1 @patch {} false)]
    (scheduler/complete! owner token (frame 180 0 0))
    (let [publication (future (scheduler/publish! owner))]
      (try
        (is (true? (deref sending 1500 false)))
        (is (= (:generation token) (:generation (deref (future (scheduler/begin-frame! owner 1 @patch {} false))
                                                       1000 nil))))
        (let [blackout (future (deliver changing true) (scheduler/begin-frame! owner 1 @patch {} true))]
          (is (true? (deref changing 1000 false)))
          (is (= :sending (deref blackout 80 :sending)))
          (deliver release true)
          (is (some? (:generation (deref blackout 1500 nil))))
          (is (nil? (scheduler/complete! owner token (frame 180 0 0))))
          (scheduler/publish! owner)
          (is (= [180 0] @output)))
        (finally (deliver release true) (deref publication 1500 nil) (scheduler/close! owner))))))

(deftest early-physical-samples-wait-for-their-slot-and-late-direct-samples-expire
  (let [physical (atom 0) sent (atom []) owner (capture physical sent)
        begin (fn [slot due start options]
                (reset! physical start)
                (scheduler/begin-frame! owner 0 @patch options false
                                        {:slot slot :started-at-ms start :deadline-ms due}))
        finish (fn [token at red]
                 (reset! physical at)
                 (scheduler/complete! owner token (frame red 0 0)))
        present (fn [at]
                  (reset! physical at)
                  (scheduler/publish! owner at)
                  (first (get-in (last @sent) [:bytes 0])))]
    (try
      (let [early (begin 1 25 15 {})]
        (is (true? (finish early 20 123)))
        (is (zero? (present 24)))
        (is (= 123 (present 25))))
      (let [late (begin 2 50 40 {})]
        (is (= 123 (present 50)))
        (is (false? (finish late 53 210))))
      (is (= 123 (present 75)))
      (is (true? (finish (begin 4 100 90 {}) 95 177)))
      (is (= 123 (present 125)) "Overdue undelivered slots cannot advance direct output")
      (is (= 1 (:missed-render-deadlines (scheduler/status owner))))
      (is (= 1 (:expired-at-publication (scheduler/status owner))))
      (let [buffered {:mode :buffered-interpolation :latency-ms 25}]
        (is (true? (finish (begin 6 150 140 buffered) 155 90)))
        (is (zero? (present 160)))
        (is (= 90 (present 175))))
      (let [fractional {:mode :buffered-interpolation :latency-ms 10}]
        (is (true? (finish (begin 8 200 190 fractional) 206 75)))
        (is (= 75 (present 225)) "The first slot after the 210 ms delayed target can use the sample")
        (is (false? (finish (begin 10 250 240 fractional) 261 155)))
        (is (= 45 (present 275)) "Fallback fades the last valid 75-byte source"))
      (finally (scheduler/close! owner)))))

(deftest scheduled-producer-and-sender-share-a-grid-without-catching-up-on-expired-slots
  (let [clock (atom 0.0) calls (atom (sorted-map)) serial (atom 0) sent (atom []) rendered (atom [])
        owner (scheduler/create {:now-ms #(deref clock)
                                 :send! (fn [u id] (swap! sent conj [@clock id (bit-and 255 (aget ^bytes (get u 0) 0))]))})
        queue! (fn [_ _ at f] (swap! calls assoc [at (swap! serial inc)] f))]
    (letfn [(until! [time]
              (loop []
                (when-let [[[at :as key] f] (first @calls)]
                  (when (<= at time)
                    (swap! calls dissoc key)
                    (swap! clock max at)
                    (f)
                    (recur))))
              (swap! clock max time))
            (render! [ticket]
              (let [id (:slot ticket) cost (if (= id 3) 55 7)
                    token (scheduler/begin-frame! owner 1 @patch {} false (assoc ticket :inputs-at-ms @clock))]
                (swap! rendered conj [id @clock (:deadline-ms ticket)])
                (until! (+ @clock cost))
                (scheduler/complete! owner token (frame id 0 0))))]
      (try
        (with-redefs [scheduler/at! queue!]
          (scheduler/start! owner 25 render!)
          (until! 175)
          (is (= [1 0.0 25.0] (first @rendered)))
          (is (< 41.0 (second (second @rendered)) 43.0) "Fresh inputs for the second 50 ms slot")
          (is (not-any? #(= 3 (last %)) @sent) "The slow render cannot take over at a later deadline")
          (is (= [25.0 50.0 75.0 100.0 125.0 150.0 175.0] (mapv first @sent)))
          (is (number? (get-in (scheduler/status owner) [:output-timing :source-input-age-ms])))
          (is (pos? (:missed-render-deadlines (scheduler/status owner))))
          (is (pos? (get-in (scheduler/status owner) [:render-timing :skipped]))))
        (finally (scheduler/close! owner))))))

(deftest blocked-wire-resumes-on-a-future-slot-with-a-single-send
  (let [clock (atom 0.0) next-call (atom nil) started (atom [])
        owner (scheduler/create {:now-ms #(deref clock)
                                 :send! (fn [_ _]
                                          (swap! started conj @clock)
                                          (when (= 1 (count @started)) (reset! clock 81.0)))})]
    (try
      (with-redefs [scheduler/at! (fn [_ _ due f] (reset! next-call [due f]))]
        (let [token (scheduler/begin-frame! owner 0 @patch {} false)]
          (scheduler/complete! owner token (frame 90 0 0)))
        (scheduler/start! owner 25)
        (is (== 25 (first @next-call)))
        (reset! clock 49.5)
        ((second @next-call))
        (is (== 100 (first @next-call)))
        (is (= [49.5 81.0] ((juxt :sent-at-ms :sent-by-ms) (:output-timing (scheduler/status owner)))))
        (reset! clock 100.0)
        ((second @next-call))
        (is (= [49.5 100.0] @started))
        (is (= 2 (:skipped-output-slots (scheduler/status owner))))
        (is (= 4 (get-in (scheduler/status owner) [:output-timing :slot]))))
      (finally (scheduler/close! owner)))))

(deftest changing-the-musical-timeline-fences-previously-buffered-output
  (let [clock (atom 0.0) sent (atom []) owner (capture clock sent)
        opts {:mode :buffered-interpolation :latency-ms 25}
        begin #(scheduler/begin-frame! owner 0 @patch opts false {:timeline-id %})]
    (try
      (let [old (begin [:playing 1])]
        (scheduler/complete! owner old (frame 211 0 0))
        (reset! clock 25.0)
        (is (= 211 (get-in (scheduler/publish! owner) [:universes 0 0])))
        (let [new (begin [:playing 2])]
          (is (> (:generation new) (:generation old)))
          (is (nil? (scheduler/complete! owner old (frame 210 0 0))))
          (is (= 0 (get-in (scheduler/publish! owner) [:universes 0 0])))
          (is (true? (scheduler/complete! owner new (frame 31 0 0))))
          (reset! clock 50.0)
          (is (= 31 (get-in (scheduler/publish! owner) [:universes 0 0])))))
      (finally (scheduler/close! owner)))))

(deftest publisher-spaces-sends-after-expensive-packet-materialization
  (let [clock (atom 0.0) next-call (atom nil) sent (atom []) owner (capture clock sent)
        materialize presentation/materialize]
    (try
      (with-redefs [scheduler/at! (fn [_ _ due f] (reset! next-call [due f]))
                    presentation/materialize (fn [packet]
                                               (reset! clock 48.0)
                                               (materialize packet))]
        (scheduler/complete! owner (scheduler/begin-frame! owner 0 @patch {} false) (frame 22 0 0))
        (scheduler/start! owner 25)
        (reset! clock 25.0)
        ((second @next-call))
        (is (== 48 (get-in (scheduler/status owner) [:output-timing :sent-at-ms])))
        (is (== 75 (first @next-call)) "A send at 50 ms would bunch two real sink invocations"))
      (finally (scheduler/close! owner)))))

(deftest packing-past-a-slot-cannot-introduce-an-expired-source
  (doseq [mode [:direct :hold-fade :buffered-interpolation]]
    (let [clock (atom 0) sent (atom []) owner (capture clock sent)
          options (cond-> {:mode mode} (= mode :buffered-interpolation) (assoc :latency-ms 10))
          pack presentation/materialize
          offer! (fn [slot red]
                   (let [deadline (* slot 25)
                         token (scheduler/begin-frame! owner 1 @patch options false
                                                       {:slot slot :started-at-ms @clock :deadline-ms deadline})]
                     (scheduler/complete! owner token (frame red 0 0))))
          publish! (fn [at] (reset! clock at) (scheduler/publish! owner at))
          red (fn [] (get-in (last @sent) [:bytes 0 0]))]
      (try
        (offer! 1 40)
        (if (= mode :buffered-interpolation)
          (do (publish! 50) (is (= 40 (red))))
          (do (publish! 25) (is (= 40 (red)))))
        (offer! 3 200)
        (when (= mode :buffered-interpolation)
          (publish! 75)) ; the new sample is still an upper endpoint
        (let [previous-sends (count @sent)
              at (if (= mode :buffered-interpolation) 100 75)]
          (with-redefs [presentation/materialize (fn [packet]
                                                  (swap! clock + 35)
                                                  (pack packet))]
            (publish! at))
          (is (= previous-sends (count @sent)) (name mode))
          (is (= 1 (:expired-before-send (scheduler/status owner))))
          (publish! (+ at 50))
          (is (<= (red) 40) "Unsent bright frames cannot become the held output"))
        (finally (scheduler/close! owner))))))

(deftest a-safety-boundary-crossed-during-the-wire-copy-is-rechecked-within-the-slot
  (let [clock (atom 0) sent (atom []) preparations (atom []) checks (atom [])
        owner (scheduler/create
               {:now-ms #(deref clock)
                :send! (fn [buffers _] (swap! sent conj [@clock (get-in (bytes-copy buffers) [0 0])]))
                :prepare-output (fn [buffers {:keys [safety-state]}]
                                  (let [^bytes data (get buffers 0)]
                                    (swap! preparations conj [@clock (bit-and 255 (aget data 0))])
                                    (when (and safety-state (>= @clock (:until-ms safety-state)))
                                      (aset-byte data 0 (unchecked-byte 196))))
                                  buffers)
                :prepare-safety-output (fn [_ _] nil)
                :output-valid-until-ms (fn [{:keys [safety-state]} at]
                                         (swap! checks conj at)
                                         (when (< at (:until-ms safety-state)) (:until-ms safety-state)))})
        copy @#'scheduler/wire-snapshot]
    (try
      (scheduler/complete! owner (scheduler/begin-frame! owner 0 @patch {} false)
                           (assoc (frame 180 0 0) :safety-state {:until-ms 26}))
      (reset! clock 25)
      (with-redefs [scheduler/wire-snapshot (fn [source buffers]
                                            (let [snapshot (copy source buffers)]
                                              (when (= @clock 25) (reset! clock 27))
                                              snapshot))]
        (let [sent (scheduler/publish! owner 25)]
          (is (= 27 (:sent-at-ms sent)))
          (is (not (:expired-before-send? sent)))))
      (is (= [25 27] @checks))
      (is (= [[25 180] [27 180]] @preparations) "Retry starts from detached original bytes")
      (is (= [[27 196]] @sent))
      (is (= 196 (get-in (bytes-copy (get-in @(:wire owner) [:last-sent :universes])) [0 0])))
      (scheduler/complete! owner (scheduler/begin-frame! owner 0 @patch {} false) (frame 92 0 0))
      (reset! clock 50)
      (scheduler/publish! owner 50)
      (is (= [25 27] @checks) "A source without safety state takes the ordinary path")
      (is (= [[27 196] [50 92]] @sent))
      (finally (scheduler/close! owner)))))

(deftest a-safety-correction-rechecks-the-remaining-boundaries-before-handoff
  (let [clock (atom 0) sent (atom []) corrected-at (atom [])
        owner (scheduler/create
               {:now-ms #(deref clock)
                :send! (fn [buffers _] (swap! sent conj [@clock (subvec (get (bytes-copy buffers) 0) 0 2)]))
                :prepare-output (fn [buffers {:keys [frame-id]}]
                                  (when (= frame-id 2) (reset! clock 76))
                                  buffers)
                :prepare-safety-output (fn [buffers {:keys [safety-state]}]
                                         (swap! corrected-at conj @clock)
                                         (let [^bytes data (get buffers 0)]
                                           (doseq [[index until] (map-indexed vector safety-state) :when (>= @clock until)]
                                             (aset-byte data index (byte 0))))
                                         buffers)
                :output-valid-until-ms (fn [{:keys [safety-state]} at] (first (drop-while #(<= % at) safety-state)))})
        copy @#'scheduler/wire-snapshot]
    (try
      (scheduler/complete! owner (scheduler/begin-frame! owner 0 @patch {} false)
                           (assoc (frame 180 170 0) :safety-state [50 77]))
      (reset! clock 25)
      (scheduler/publish! owner 25)
      (scheduler/complete! owner (scheduler/begin-frame! owner 0 @patch {} false) (frame 255 255 0))
      (reset! clock 50)
      (with-redefs [scheduler/wire-snapshot (fn [{:keys [frame-id] :as source} buffers]
                                            (let [snapshot (copy source buffers)]
                                              (when (and (= frame-id 1) (= @clock 76)) (reset! clock 78))
                                              snapshot))]
        (is (= {:expired-before-send? true :safety-output? true :sent-at-ms 78}
               (select-keys (scheduler/publish! owner 50) [:expired-before-send? :safety-output? :sent-at-ms]))))
      (is (= [76 78] @corrected-at))
      (is (= [[25 [180 170]] [78 [0 0]]] @sent))
      (finally (scheduler/close! owner)))))

(deftest preparation-uses-the-context-owned-by-the-publication-gate
  (let [clock (atom 0) contexts (atom [])
        owner (scheduler/create
               {:now-ms #(deref clock)
                :send! (fn [_ _])
                :prepare-output (fn [buffers {:keys [output-context]}]
                                  (swap! contexts conj output-context)
                                  (when (= :next-patch output-context) (reset! clock 76))
                                  buffers)
                :prepare-safety-output (fn [buffers {:keys [output-context stale-source?]}]
                                         (swap! contexts conj [output-context stale-source?])
                                         buffers)})
        begin (fn [epoch context] (scheduler/begin-frame! owner epoch @patch {} false {:output-context context}))]
    (try
      (let [first-gate (begin 0 :first-patch)
            continuing (begin 0 :not-installed)]
        (is (= (:generation first-gate) (:generation continuing)))
        (scheduler/complete! owner continuing (frame 180 0 0)))
      (reset! clock 25)
      (scheduler/publish! owner 25)
      (scheduler/complete! owner (begin 1 :next-patch) (frame 255 0 0))
      (reset! clock 50)
      (is (:safety-output? (scheduler/publish! owner 50)))
      (is (= [:first-patch :next-patch [:next-patch true]] @contexts))
      (finally (scheduler/close! owner)))))

(deftest a-buffered-sample-can-survive-packet-packing-in-an-earlier-slot
  (let [clock (atom 0) sent (atom []) owner (capture clock sent)
        pack presentation/materialize
        options {:mode :buffered-interpolation :latency-ms 26}]
    (try
      (let [token (scheduler/begin-frame! owner 1 @patch options false
                                          {:slot 1 :started-at-ms 0 :deadline-ms 25})]
        (scheduler/complete! owner token (frame 144 0 0)))
      (reset! clock 25)
      (with-redefs [presentation/materialize (fn [packet] (reset! clock 58) (pack packet))]
        (scheduler/publish! owner 25))
      (is (empty? @sent))
      (reset! clock 75)
      (scheduler/publish! owner 75)
      (is (= [144] (mapv #(get-in % [:bytes 0 0]) @sent)))
      (finally (scheduler/close! owner)))))

(deftest a-completion-arriving-during-an-expired-send-survives
  (let [clock (atom 0) sent (atom []) owner (capture clock sent)
        pack presentation/materialize
        offer! (fn [slot red]
                 (let [token (scheduler/begin-frame! owner 1 @patch {} false
                                                     {:slot slot :started-at-ms @clock
                                                      :deadline-ms (* slot 25)})]
                   (scheduler/complete! owner token (frame red 0 0))))]
    (try
      (offer! 1 80)
      (reset! clock 25)
      (with-redefs [presentation/materialize (fn [packet]
                                               (reset! clock 61)
                                               (offer! 3 190)
                                               (pack packet))]
        (scheduler/publish! owner 25))
      (reset! clock 75)
      (scheduler/publish! owner 75)
      (is (= [190] (mapv #(get-in % [:bytes 0 0]) @sent)))
      (scheduler/begin-frame! owner 1 @patch {} true)
      (with-redefs [presentation/materialize (fn [packet] (swap! clock + 50) (pack packet))]
        (scheduler/publish! owner 75))
      (is (= [190 0] (mapv #(get-in % [:bytes 0 0]) @sent)) "Explicit blackout reaches the sink")
      (finally (scheduler/close! owner)))))

(deftest acknowledgement-keeps-newer-completions-and-close-fences-the-mailbox
  (let [clock (atom 0) sent (atom []) owner (capture clock sent)
        offer! (fn [id]
                 (reset! clock id)
                 (scheduler/complete! owner (scheduler/begin-frame! owner 0 @patch {} false) (frame id 0 0)))
        pack presentation/materialize freeze presentation/freeze-frame]
    (try
      (offer! 1)
      (with-redefs [presentation/materialize (fn [packet]
                                               (doseq [n [2 3 4]] (offer! n))
                                               (pack packet))]
        (scheduler/publish! owner))
      (is (= 3 (:pending (scheduler/status owner))))
      (scheduler/publish! owner)
      (is (= [1 4] (mapv #(get-in % [:bytes 0 0]) @sent)))
      (is (zero? (:pending (scheduler/status owner))))
      (with-redefs [presentation/freeze-frame (fn [token rendered]
                                                (scheduler/close! owner)
                                                (freeze token rendered))]
        (is (nil? (offer! 5))))
      (is (zero? (:pending (scheduler/status owner))))
      (finally (scheduler/close! owner)))))

(deftest three-future-endpoints-cannot-evict-the-physical-lower-source
  (doseq [[mode expected] [[:direct 80] [:hold-fade 60] [:buffered-interpolation 110]]]
    (let [clock (atom 0) sent (atom []) owner (capture clock sent)
          options {:mode mode :latency-ms 25 :fade-ms 100}
          offer! (fn [slot red]
                   (let [token (scheduler/begin-frame! owner 1 @patch options false
                                                       {:slot slot :started-at-ms @clock :deadline-ms (* 25 slot)})]
                     (scheduler/complete! owner token (frame red 0 0))))
          publish! (fn [at] (reset! clock at) (scheduler/publish! owner at))]
      (try
        (offer! 1 80)
        (publish! (if (= mode :buffered-interpolation) 50 25))
        (doseq [slot [5 6 7]] (offer! slot 200))
        (let [packet (publish! 75)]
          (is (= 1 (:frame-id packet)) (name mode))
          (is (= expected (get-in packet [:universes 0 0])) (name mode)))
        (finally (scheduler/close! owner))))))

(deftest sender-includes-final-channel-preparation-and-spaces-from-completed-handoff
  (let [clock (atom 0) next-call (atom nil) sent (atom [])
        owner (scheduler/create {:now-ms #(deref clock)
                                 :prepare-output (fn [buffers {:keys [frame-id]}]
                                                   (when (= frame-id 1) (reset! clock 59))
                                                   buffers)
                                 :send! (fn [_ id]
                                          ;; A transport can start working after the caller's
                                          ;; final clock sample because its thread was preempted.
                                          (swap! clock + 15)
                                          (swap! sent conj [id @clock]))})
        offer! (fn [id] (scheduler/complete! owner (scheduler/begin-frame! owner 1 @patch {} false)
                                            (frame id 0 0)))]
    (try
      (with-redefs [scheduler/at! (fn [_ _ due f] (reset! next-call [due f]))]
        (offer! 1)
        (scheduler/start! owner 25)
        (reset! clock 25)
        ((second @next-call))
        (is (empty? @sent) "A stall in host channel preparation expires the old packet")
        (is (== 75 (first @next-call)))
        (offer! 2)
        (reset! clock 75)
        ((second @next-call))
        (is (= [[2 90]] @sent))
        (is (== 125 (first @next-call)) "A 100 ms callback could be only ten ms after the last entry"))
      (finally (scheduler/close! owner)))))

(deftest failed-handoff-spaces-the-next-send-even-after-partial-delivery
  (let [clock (atom 0.0) next-call (atom nil) sent (atom [])
        owner (scheduler/create {:now-ms #(deref clock)
                                 :send! (fn [_ _]
                                          (if (empty? @sent)
                                            (do (reset! clock 49.9)
                                                (swap! sent conj @clock)
                                                (throw (ex-info "Transport failed after sending one universe" {})))
                                            (swap! sent conj @clock)))})]
    (try
      (with-redefs [scheduler/at! (fn [_ _ due f] (reset! next-call [due f]))]
        (scheduler/complete! owner (scheduler/begin-frame! owner 1 @patch {} false) (frame 180 0 0))
        (scheduler/start! owner 25)
        (reset! clock 25.0)
        ((second @next-call))
        (is (= 1 (:failed-publications (scheduler/status owner))))
        (is (= {:failed? true :finished-at-ms 49.9}
               (select-keys (:output-timing (scheduler/status owner)) [:failed? :finished-at-ms])))
        (is (== 75 (first @next-call)))
        (reset! clock (first @next-call))
        ((second @next-call))
        (is (= [49.9 75.0] @sent))
        (is (= 1 (:skipped-output-slots (scheduler/status owner)))))
      (finally (scheduler/close! owner)))))

(deftest overdue-safety-correction-uses-the-last-physical-bytes
  (let [clock (atom 0.0) next-call (atom nil) sent (atom [])
        owner (scheduler/create
               {:now-ms #(deref clock)
                :prepare-output (fn [buffers {:keys [frame-id]}]
                                  (when (> frame-id 1) (swap! clock + 26))
                                  buffers)
                :prepare-safety-output (fn [buffers {:keys [frame-id safety-state]}]
                                         (is (= {:source frame-id} safety-state))
                                         (let [^bytes buffer (get buffers 0)]
                                           (when-not (zero? (aget buffer 1))
                                             (aset-byte buffer 1 (byte 0))
                                             buffers)))
                :send! (fn [buffers id]
                         (let [^bytes buffer (get buffers 0)]
                           (swap! sent conj [id (bit-and 255 (aget buffer 0)) (bit-and 255 (aget buffer 1))])
                           ;; A transport owns these arrays and may reuse them.
                           (aset-byte buffer 0 (byte 0))))})
        offer! (fn [slot red]
                 (let [token (scheduler/begin-frame! owner 1 @patch {} false
                                                     {:slot slot :started-at-ms @clock :deadline-ms (* 25 slot)})]
                   (scheduler/complete! owner token (assoc (frame red 200 0) :safety-state {:source (:frame-id token)}))))
        run-next! (fn [] (reset! clock (first @next-call)) ((second @next-call)))]
    (try
      (with-redefs [scheduler/at! (fn [_ _ due f] (reset! next-call [due f]))]
        (offer! 1 10)
        (scheduler/start! owner 25)
        (run-next!)
        (offer! 2 20)
        (run-next!)
        (is (= [[1 10 200] [1 10 0]] @sent))
        (is (= {:frame-id 1 :expired-before-send? true :safety-output? true :sent-by-ms 76.0}
               (select-keys (:output-timing (scheduler/status owner))
                            [:frame-id :expired-before-send? :safety-output? :sent-by-ms])))
        (is (== 100 (first @next-call)))
        (offer! 4 30)
        (run-next!)
        (is (= [[1 10 200] [1 10 0]] @sent) "An already corrected held packet needs no extra send")
        (is (= 1 (:published (scheduler/status owner))))
        (is (= 1 (:safety-publications (scheduler/status owner))))
        (is (= 2 (:expired-before-send (scheduler/status owner)))))
      (finally (scheduler/close! owner)))))

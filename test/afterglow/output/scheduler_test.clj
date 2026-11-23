(ns afterglow.output.scheduler-test
  (:require [clojure.test :refer [deftest is]]
            [afterglow.render.frame :as render]
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

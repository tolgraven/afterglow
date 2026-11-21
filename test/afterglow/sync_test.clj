(ns afterglow.sync-test
  (:require [clojure.test :refer :all]
            [afterglow.sync :as sync]
            [afterglow.sync.session :as session]
            [afterglow.sync.beat-link :as dj])
  (:import [java.net DatagramPacket InetAddress]
           [org.deepsymmetry.beatlink Beat DeviceAnnouncement]
           [java.util.concurrent CountDownLatch TimeUnit]))

(defn near? [a b] (< (Math/abs (double (- a b))) 1.0e-7))
(defn envelope [id] {:show-id :show :epoch 1 :time-ms 0.0 :command-id id})
(defn callbacks [commands events]
  (let [id (atom 0)]
    {:events! #(swap! events conj %) :commands! #(swap! commands into %)
     :envelope! #(envelope (str "capture-" (swap! id inc)))}))
(defn fake-midi [opens closes receiver sent]
  (fn [_ _]
    {:open! (fn [receive!] (swap! opens inc) (reset! receiver receive!) :owned)
     :close! (fn [handle] (is (= :owned handle)) (swap! closes inc))
     :send! (fn [_ bytes] (swap! sent into bytes))}))

(def midi-config {:selected-source :midi-clock :midi {:enabled? true :input-index 0 :control? true}})

(defn send-midi! [manager at bytes]
  (is (session/ingest! manager {:type :midi/message :source-id :midi-clock :time-ms at :bytes bytes})))

(deftest explicit-start-ticks-stop-and-late-input-ownership
  (let [opens (atom 0) closes (atom 0) receive (atom nil) now (atom 0.0)
        manager (sync/create-manager {:config midi-config :now-ms #(deref now)
                                      :midi-factory (fake-midi opens closes receive (atom []))})
        commands (atom []) events (atom [])]
    (try
      (is (false? (session/ingest! manager {:type :anything})))
      (sync/start! manager (callbacks commands events))
      (is (session/flush! manager))
      (is (= 1 @opens))
      (is (thrown? clojure.lang.ExceptionInfo (sync/configure! manager {})))
      (send-midi! manager 0 [0xfa])
      (doseq [tick (range 25)] (send-midi! manager (* tick (/ 500.0 24)) [0xf8]))
      (reset! now 500.0)
      (is (session/flush! manager))
      (let [clock (:clock (session/clock-at manager 500))]
        (is (near? 1.0 (:beat clock))) (is (near? 120 (:bpm clock)))
        (is (near? 1.0 (:confidence clock))) (is (:playing? clock)))
      (send-midi! manager 500 [0xfc])
      (is (session/flush! manager))
      (is (false? (get-in (session/clock-at manager 1000) [:clock :playing?])))
      (is (:stopped? (sync/stop! manager)))
      (is (= :disconnected (:status (session/clock-at manager 1000))))
      (is (= 1 @closes))
      (is (false? (@receive {:type :midi/message :source-id :midi-clock :time-ms 1100 :bytes [0xfa]})))
      (is (:stopped? (sync/stop! manager)))
      (is (= 1 @closes))
      (finally (sync/close! manager)))))

(deftest real-beat-link-getters-convert-packet-age-and-announcement-identity
  ;; Construct actual library data objects; no singleton listeners or sockets.
  (let [bytes (byte-array 96) address (InetAddress/getByAddress (byte-array [10 0 0 2]))]
    (doseq [[i value] [[0x21 2] [0x55 0x10] [0x5a 0x2e] [0x5b 0xe0] [0x5c 3]]]
      (aset-byte bytes i (unchecked-byte value)))
    (System/arraycopy (.getBytes "CDJ-3000" "UTF-8") 0 bytes 0x0b 8)
    (let [beat (Beat. (DatagramPacket. bytes 96 address 50001))
          data (dj/beat-data beat 1000 (+ (.getTimestamp beat) 2500000))]
      (is (= 997.5 (:time-ms data))) (is (= 2.5 (:packet-age-ms data)))
      (is (= 120.0 (:bpm data))) (is (= 3 (:beat-within-bar data)))
      (is (= {:device-number 2 :device-name "CDJ-3000" :address "10.0.0.2"} (:peer data))))
    (let [packet (byte-array 54)]
      (aset-byte packet 0x24 (byte 2))
      (doseq [[index b] (map-indexed vector [0 1 2 3 4 255])] (aset-byte packet (+ 0x26 index) (unchecked-byte b)))
      (System/arraycopy (.getBytes "CDJ-3000" "UTF-8") 0 packet 0x0c 8)
      (is (= {:device-number 2 :device-name "CDJ-3000" :address "10.0.0.2"
              :hardware-address "00:01:02:03:04:ff" :observed-at-ms 12}
             (dj/announcement-data (DeviceAnnouncement. (DatagramPacket. packet 54 address 50000)) 12))))))

(deftest beat-link-pairing-does-not-follow-a-different-player
  (let [peer {:device-number 2 :address "10.0.0.2" :hardware-address "00:01:02:03:04:ff"}
        manager (sync/create-manager {:now-ms (constantly 1000)
                                      :config {:selected-source :beat-link
                                               :beat-link {:peer (select-keys peer [:device-number :hardware-address]) :align-bars? true}}})]
    (try
      (sync/start! manager {:events! identity}) (is (session/flush! manager))
      (session/ingest! manager {:type :peer/found :peer peer})
      (session/ingest! manager {:type :beat-link/beat :source-id :beat-link :time-ms 1000 :bpm 120
                            :beat-within-bar 3 :bar-meaningful? true :peer (assoc peer :device-number 3)})
      (is (session/flush! manager)) (is (= :waiting (:status (session/clock-at manager 1000))))
      (session/ingest! manager {:type :beat-link/beat :source-id :beat-link :time-ms 1000 :bpm 120
                            :beat-within-bar 3 :bar-meaningful? true :peer peer})
      (is (session/flush! manager)) (is (= 2.0 (get-in (session/clock-at manager 1000) [:clock :beat])))
      (session/ingest! manager {:type :peer/lost :peer peer}) (is (session/flush! manager))
      (is (= :disconnected (:status (session/clock-at manager 1000))))
      (is (empty? (:peers (sync/status manager))))
      (finally (sync/close! manager)))))

(deftest cancellation-interrupts-acquisition-and-closes-already-owned-resources
  (let [entered (promise) release (CountDownLatch. 1) closed (atom 0)
        manager (sync/create-manager {:config {:beat-link {:enabled? true} :midi {:enabled? true :input-index 0}}
                                      :beat-link-factory (fn [& _] {:open! (fn [_] :dj) :close! (fn [_] (swap! closed inc))})
                                      :midi-factory (fn [& _] {:open! (fn [_] (deliver entered true) (.await release 5 TimeUnit/SECONDS) :midi)
                                                             :close! (fn [_] (swap! closed inc))})})]
    (try
      (sync/start! manager {:events! identity})
      (is (true? (deref entered 1000 false)))
      (is (:stopped? (sync/stop! manager)))
      (is (= 1 @closed))
      (is (false? (:active? (sync/status manager))))
      (finally (.countDown release) (sync/close! manager)))))

(deftest open-failure-cleans-prior-resources-and-can-be-retried
  (let [closed (atom 0) attempts (atom 0)
        manager (sync/create-manager {:config {:beat-link {:enabled? true} :midi {:enabled? true :input-index 0}}
                                      :beat-link-factory (fn [& _] {:open! (fn [_] :beatlink) :close! (fn [_] (swap! closed inc))})
                                      :midi-factory (fn [& _] (swap! attempts inc) (throw (Exception. "injected open failure")))})]
    (try
      (dotimes [_ 2]
        (let [run (sync/start! manager {:events! identity})]
          (is (= :error (:status (deref (:result run) 2000 nil))))
          (is (false? (:active? (sync/status manager))))))
      (is (= 2 @closed @attempts))
      (finally (sync/close! manager)))))

(deftest overflow-reports-lost-phase-and-recovers-only-on-explicit-resync
  (let [gate (CountDownLatch. 1) entered (promise) overflow (promise) events (atom []) now (atom 0)
        manager (sync/create-manager {:config {:selected-source :midi-clock} :queue-capacity 8 :now-ms #(deref now)})]
    (try
      (sync/start! manager {:events! (fn [event]
                                      (swap! events conj event)
                                      (when (= :sync/input-overflow (:type event)) (deliver overflow true))
                                      (when (and (= :sync/clock (:type event)) (not (realized? entered)))
                                        (deliver entered true) (.await gate 2 TimeUnit/SECONDS)))})
      (send-midi! manager 0 [0xfa]) (is (true? (deref entered 1000 false)))
      (doseq [tick (range 8)] (is (session/ingest! manager {:type :midi/message :source-id :midi-clock :time-ms tick :bytes [0xf8]})))
      (is (false? (session/ingest! manager {:type :midi/message :source-id :midi-clock :time-ms 9 :bytes [0xf8]})))
      (reset! now 100) (.countDown gate)
      (is (true? (deref overflow 1000 false)))
      (is (= 1 (get-in (sync/status manager) [:metrics :dropped-input-events])))
      (is (some #(= :sync/input-overflow (:type %)) @events))
      (is (false? (get-in (session/clock-at manager 100) [:clock :playing?])))
      ;; The overflow callback runs before dequeueing the old backlog. Wait for
      ;; a barrier using its queue directly so test admission cannot add a loss.
      (let [barrier (promise) run (:active @(:state manager)) queue (:queue run)]
        (is (.offer queue {:type :barrier :promise barrier ::session/generation @(:binding-generation run)} 1000 TimeUnit/MILLISECONDS))
        (is (true? (deref barrier 1000 false))))
      (send-midi! manager 100 [0xfa]) (send-midi! manager 100 [0xf8]) (is (session/flush! manager))
      (is (true? (get-in (session/clock-at manager 100) [:clock :playing?])))
      (finally (.countDown gate) (sync/close! manager)))))

(deftest custom-source-retains-ownership-until-outstanding-io-really-exits
  (let [entered (promise) released (CountDownLatch. 1) closes (atom 0)
        adapter {:defaults {:enabled? true :source-id :probe}
                 :transport (fn [_ _ _] {:open! (fn [_] :probe)
                                         :close! (fn [_] (swap! closes inc))})
                 :events #{:probe/hold}
                 :receive! (fn [manager run _ _]
                             (session/enqueue-io!
                              manager run
                              (fn []
                                (deliver entered true)
                                ;; Simulate a device that acknowledges cancellation late.
                                (loop []
                                  (when-not (try (.await released 10 TimeUnit/MILLISECONDS)
                                                 (catch InterruptedException _ false))
                                    (recur))))))}
        manager (sync/create-manager {:adapters {:probe adapter} :config {:selected-source :probe}})]
    (try
      (let [first-run (sync/start! manager {:events! identity})]
        (is (true? (session/ingest! manager {:type :probe/hold})))
        (is (true? (deref entered 2000 false)))
        (is (false? (:stopped? (sync/stop! manager 20))))
        (is (thrown? clojure.lang.ExceptionInfo (sync/start! manager {:events! identity})))
        (.countDown released)
        (is (true? (:terminated? (deref (:result first-run) 2000 nil))))
        (is (= 1 @closes))
        (let [second-run (sync/start! manager {:events! identity})]
          (is (true? (session/flush! manager)))
          (is (:stopped? (sync/stop! manager 100 (:run-id first-run))))
          (is (= (:run-id second-run) (sync/active-run-id manager)))
          (is (:stopped? (sync/stop! manager)))
          (is (= 2 @closes))))
      (finally (.countDown released) (sync/close! manager)))))

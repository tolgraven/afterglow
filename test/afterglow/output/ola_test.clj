(ns afterglow.output.ola-test
  (:require [clojure.test :refer [deftest is]]
            [afterglow.output.ola :as ola]))

(defn unsigned [buffer] (mapv #(bit-and 255 %) buffer))

(defn ola-body [packet]
  (let [header (-> (java.nio.ByteBuffer/wrap packet)
                   (.order (java.nio.ByteOrder/nativeOrder)) .getInt)]
    (is (= 1 (unsigned-bit-shift-right header 28)))
    (is (= (- (alength ^bytes packet) 4) (bit-and header 0x0fffffff)))
    (subvec (unsigned packet) 4)))

(deftest ola-streaming-rpc-matches-protobuf-wire-contract
  ;; Rpc.proto: STREAM_REQUEST=10. Ola.proto: universe field 1, data field 2.
  ;; Streaming deliberately expects no Ack (not an UpdateDmxData REQUEST).
  (is (= [8 10 16 0 26 13 83 116 114 101 97 109 68 109 120 68 97 116 97
          34 6 8 1 18 2 0 255]
         (ola-body (ola/ola-stream-packet 1 0 [0 255]))))
  (is (= [8 10 16 255 255 255 255 15 26 13 83 116 114 101 97 109 68 109 120 68 97 116 97
          34 7 8 255 255 3 18 1 128]
         (ola-body (ola/ola-stream-packet 65535 4294967295 [-128]))))
  (let [values (byte-array (map unchecked-byte (range 512)))
        before (aclone values)
        packet (ola/ola-stream-packet 0 128 values)]
    (is (= (vec packet) (vec (ola/ola-stream-packet 0 128 (unsigned values)))))
    (is (= (vec before) (vec values)))
    (aset-byte values 0 (byte 99))
    (is (= (unsigned before) (vec (take-last 512 (ola-body packet)))))))

(deftest ola-rejects-invalid-universes-request-ids-and-channel-data
  (doseq [[universe request-id values]
          [[-1 0 [0]] [65536 0 [0]] [1.5 0 [0]] [1 -1 [0]] [1 4294967296 [0]]
           [1 0.5 [0]] [1 0 []] [1 0 (byte-array 513)] [1 0 [-129]] [1 0 [256]]
           [1 0 [0.5]] [1 0 [Double/NaN]]]]
    (is (thrown? clojure.lang.ExceptionInfo (ola/ola-stream-packet universe request-id values)))))

(deftest ola-injected-transport-is-owned-and-repeated-frames-still-send
  (let [opened (atom []) writes (atom []) closes (atom 0)
        values (byte-array [42])
        sink (ola/open-ola! {:open-transport! (fn [options]
                                                 (swap! opened conj options)
                                                 {:write! #(swap! writes conj %)
                                                  :close! #(swap! closes inc)})})]
    (try
      (is (= [{:host "127.0.0.1" :port 9010 :connect-timeout-ms 1000 :write-timeout-ms 1000}]
             @opened))
      (is (= {:type :ola :host "127.0.0.1" :port 9010 :method :stream-dmx-data} (:description sink)))
      ((:send! sink) {2 values 1 [255]} 17)
      ((:send! sink) {2 [0]} 17)
      (aset-byte values 0 (byte 33))
      (is (= [(mapv vec [(ola/ola-stream-packet 1 0 [255]) (ola/ola-stream-packet 2 1 [42])])
              [(vec (ola/ola-stream-packet 2 2 [0]))]]
             (mapv #(mapv vec %) @writes)))
      ((:send! sink) {} 18)
      (is (= 2 (count @writes)))
      (is (thrown? clojure.lang.ExceptionInfo ((:send! sink) {1 [0] 2 [999]} 19)))
      (is (= 2 (count @writes)) "Invalid later universe cannot partially publish a frame")
      (finally ((:close! sink))))
    ((:close! sink))
    (is (= 1 @closes))
    (is (thrown? java.io.IOException ((:send! sink) {1 [0]} 20)))))

(deftest ola-invalid-options-never-open-transport
  (doseq [options [{:host ""} {:port 0} {:port 65536} {:connect-timeout-ms 0}
                   {:write-timeout-ms 0} {:write-timeout-ms 1.5} {:write-timeout-ms 60001}]]
    (let [opens (atom 0)]
      (is (thrown? clojure.lang.ExceptionInfo
                   (ola/open-ola! (assoc options :open-transport! #(swap! opens inc)))))
      (is (zero? @opens)))))

(deftest ola-transport-failure-retires-only-that-sink
  (let [closes (atom 0) writes (atom 0)
        error (java.io.IOException. "disconnected during frame")
        sink (ola/open-ola! {:open-transport! (fn [_]
                                                  {:write! (fn [_] (swap! writes inc) (throw error))
                                                   :close! #(swap! closes inc)})})]
    (is (identical? error (try ((:send! sink) {1 [0]} 1) (catch java.io.IOException e e))))
    (is (= 1 @closes))
    (is (thrown? java.io.IOException ((:send! sink) {1 [0]} 2)))
    ((:close! sink))
    (is (= 1 @closes))
    (is (= 1 @writes))))

(deftest closing-ola-interrupts-pending-transport-without-waiting-for-write-lock
  (let [entered (promise) released (promise) closes (atom 0)
        sink (ola/open-ola! {:open-transport! (fn [_]
                                                  {:write! (fn [_] (deliver entered true)
                                                             (deref released 2000 false)
                                                             (throw (java.io.IOException. "closed")))
                                                   :close! #(do (swap! closes inc) (deliver released true))})})
        sender (future (try ((:send! sink) {1 [0]} 0) (catch java.io.IOException _ :closed)))]
    (try
      (is (true? (deref entered 2000 false)))
      ((:close! sink))
      (is (= :closed (deref sender 2000 :timed-out)))
      (is (= 1 @closes))
      (finally ((:close! sink)) (future-cancel sender)))))

(defn read-ola-packet [^java.io.DataInputStream stream]
  (let [header (byte-array 4)]
    (.readFully stream header)
    (let [size (bit-and 0x0fffffff (-> (java.nio.ByteBuffer/wrap header)
                                      (.order (java.nio.ByteOrder/nativeOrder)) .getInt))
          packet (byte-array (+ 4 size))]
      (System/arraycopy header 0 packet 0 4)
      (.readFully stream packet 4 size)
      packet)))

(deftest ola-owned-tcp-loopback-transports-complete-rpcs-and-closes-connection
  (with-open [server (java.net.ServerSocket. 0 1 (java.net.InetAddress/getByName "127.0.0.1"))]
    (.setSoTimeout server 2000)
    (let [sink (ola/open-ola! {:host "127.0.0.1" :port (.getLocalPort server)})]
      (try
        (with-open [peer (.accept server)
                    stream (java.io.DataInputStream. (.getInputStream peer))]
          (.setSoTimeout peer 2000)
          ((:send! sink) {65535 (byte-array 512) 1 [23 255 0]} 8)
          (is (= (vec (ola/ola-stream-packet 1 0 [23 255 0])) (vec (read-ola-packet stream))))
          (is (= (vec (ola/ola-stream-packet 65535 1 (byte-array 512))) (vec (read-ola-packet stream))))
          ((:send! sink) {1 [0]} 8)
          (is (= (vec (ola/ola-stream-packet 1 2 [0])) (vec (read-ola-packet stream))))
          ((:close! sink))
          (is (= -1 (.read stream))))
        (finally ((:close! sink)))))))

(deftest ola-write-deadline-closes-a-backpressured-connection
  (with-open [server (java.net.ServerSocket. 0 1 (java.net.InetAddress/getByName "127.0.0.1"))]
    (.setReceiveBufferSize server 1024)
    (.setSoTimeout server 2000)
    (let [sink (ola/open-ola! {:host "127.0.0.1" :port (.getLocalPort server) :write-timeout-ms 50})]
      (try
        (with-open [peer (.accept server)]
          ;; More than the socket send buffer, while the owned peer never reads.
          ;; This tests backpressure behavior, not a performance threshold.
          (let [frame (zipmap (range 8192) (repeat (byte-array 512)))
                sender (future (try ((:send! sink) frame 1) :unexpected-success
                                    (catch java.net.SocketTimeoutException _ :deadline)))]
            (try
              (is (= :deadline (deref sender 5000 :timed-out)))
              (is (thrown? java.io.IOException ((:send! sink) {1 [0]} 2)))
              (finally ((:close! sink)) (future-cancel sender)))))
        (finally ((:close! sink)))))))

(ns afterglow.rdm.transport-test
  (:require [clojure.test :refer [deftest is]]
            [afterglow.rdm.codec :as codec]
            [afterglow.rdm.transport :as transport])
  (:import [java.net ServerSocket InetAddress SocketTimeoutException]
           [java.io DataInputStream]
           [java.nio ByteBuffer ByteOrder]))

(def device {:universe 1 :uid "1234:01020304" :sub-device 0})

(defn ack [request data]
  {:response-code 0 :response-type 0 :pid (:pid request) :sub-device (:sub-device request 0)
   :command-class (if (= :set (:command request)) 1 0) :data data})

(deftest request-wire-layout-and-response-correlation
  (is (= [8 1 18 8 8 180 36 21 4 3 2 1 24 0 32 240 1 42 2 0 100 48 1]
         (codec/request-body "RDMCommand" (merge device {:pid 0xf0 :command :set :data [0 100]}))))
  (is (= "1234:01020304" (codec/decode-uid [8 180 36 21 4 3 2 1])))
  (doseq [request [(merge device {:pid 0x60 :sub-device 513}) (merge device {:pid 0x60 :data [256]})
                   (merge device {:pid 0x60 :uid "invalid"})]]
    (is (thrown? clojure.lang.ExceptionInfo (codec/request-body "RDMCommand" request))))
  (is (thrown? clojure.lang.ExceptionInfo
               (codec/decode-reply 2 "RDMCommand" (merge device {:pid 0x60}) [8 2 16 1 34 0])))
  (is (thrown? clojure.lang.ExceptionInfo (codec/parse-protobuf [10 4 0])))
  (is (= 200 (count (codec/decode-value 0x50 (vec (repeat 400 0))))))
  (is (thrown? clojure.lang.ExceptionInfo (codec/decode-value 0x60 [1]))))

(deftest actual-loopback-connection-handles-fragmented-protobuf
  (with-open [server (ServerSocket. 0 1 (InetAddress/getLoopbackAddress))]
    (let [reply (codec/protobuf [[1 0 2] [2 0 1]
                                 [4 2 (codec/protobuf [[1 0 1] [2 2 [8 180 36 21 4 3 2 1]]])]])
          header (.array (doto (ByteBuffer/allocate 4) (.order (ByteOrder/nativeOrder))
                           (.putInt (bit-or 0x10000000 (count reply)))))
          peer (future
                 (with-open [socket (.accept server)]
                   (.setSoTimeout socket 1000)
                   (let [input (DataInputStream. (.getInputStream socket))
                         request-header (byte-array 4)
                         _ (.readFully input request-header)
                         body (byte-array (codec/message-size request-header))
                         _ (.readFully input body)
                         output (.getOutputStream socket)]
                     (doseq [b (concat header reply)]
                       (.write output (int (bit-and 255 b)))
                       (.flush output))
                     (mapv #(bit-and 255 %) body))))
          deadline (+ (System/nanoTime) 5000000000)
          connection (transport/open! {:host (.getHostAddress (.getInetAddress server))
                                       :port (.getLocalPort server) :timeout-ms 1000}
                                      deadline (fn [_]))]
      (try
        (is (= [(:uid device)] (:uids ((:request! connection) "ForceDiscovery" {:universe 1 :full? true}))))
        (let [request (codec/parse-protobuf (deref peer 2000 []))]
          (is (= 1 (codec/field request 2)))
          (is (= (vec (.getBytes "ForceDiscovery" "US-ASCII")) (codec/field request 3)))
          (is (= [8 1 16 1] (codec/field request 4))))
        (finally ((:close! connection)) (future-cancel peer))))))

(deftest queued-set-completes-without-resending-and-preserves-nack
  (let [calls (atom []) responses (atom [(assoc (ack (assoc device :sub-device 3 :pid 0x82 :command :set) [0 0]) :response-type 1)
                                       (ack (assoc device :sub-device 3 :pid 0x82 :command :set) [])])
        request! (fn [_ request] (swap! calls conj request) (let [r (first @responses)] (swap! responses subvec 1) r))
        result (transport/command! request! (assoc device :sub-device 3 :pid 0x82 :command :set :data [65])
                                   (+ (System/nanoTime) 1000000000) (constantly true))]
    (is (= :ack (:status result)))
    (is (= [:set :get] (mapv :command @calls)))
    (is (= [0x82 0x20] (mapv :pid @calls)))
    (is (= 0 (:sub-device (second @calls)))))
  (is (= :unknown-pid (:reason (transport/command! (fn [_ request] (assoc (ack request [0 0]) :response-type 2))
                                                   (assoc device :pid 0x9999) (+ (System/nanoTime) 1000000000) (constantly true)))))
  (is (thrown? clojure.lang.ExceptionInfo
               (transport/command! (fn [_ request] (assoc (ack request []) :command-class 1))
                                   (assoc device :pid 0x60) (+ (System/nanoTime) 1000000000) (constantly true)))))

(deftest delayed-ack-cannot-exceed-absolute-deadline
  (is (thrown? SocketTimeoutException
               (transport/command! (fn [_ request] (assoc (ack request [255 255]) :response-type 1))
                                   (assoc device :pid 0x60) (+ (System/nanoTime) 1000000000) (constantly true)))))

(deftest expired-or-cancelled-command-does-not-send-a-set
  (let [sent (atom [])
        request! (fn [_ command] (swap! sent conj command) (ack command []))
        command (assoc device :pid 0xf0 :command :set :data [0 2])]
    (is (thrown? SocketTimeoutException
                 (transport/command! request! command (System/nanoTime) (constantly true))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (transport/command! request! command (+ (System/nanoTime) 1000000000) (constantly false))))
    (is (empty? @sent))))

(deftest delayed-commands-consume-only-the-matching-nack
  (let [command (assoc device :pid 0x82 :command :set :sub-device 2 :data [65])
        delayed (assoc (ack command [0 0]) :response-type 1)
        nack (fn [request] (assoc (ack request [0 4]) :response-type 2))
        queue (assoc device :pid 0x20 :command :get)
        run (fn [responses]
              (let [remaining (atom responses)]
                (transport/command! (fn [_ _] (first (first (swap-vals! remaining next)))) command
                                    (+ (System/nanoTime) 1000000000) (constantly true))))]
    (is (= :nack (:status (run [delayed (nack (assoc command :sub-device 1))
                                (nack (assoc command :command :get)) (nack (assoc command :pid 0x83))
                                (nack command)]))))
    (is (= :queue-nack (:status (run [delayed (nack queue)]))))
    (is (= :ack (:status (run [delayed (nack (assoc command :sub-device 1)) (ack command [])]))))))

(deftest cancellation-releases-the-io-worker-during-ack-timer
  (let [waiting (promise) continue? (atom true) attempts (atom 0)
        job (future
              (try (transport/command! (fn [_ r] (swap! attempts inc) (assoc (ack r [0 30]) :response-type 1))
                                       (assoc device :pid 0x60) (+ (System/nanoTime) 5000000000)
                                       #(do (when (pos? @attempts) (deliver waiting true)) @continue?))
                   (catch clojure.lang.ExceptionInfo e (:rdm/error (ex-data e)))))]
    (try
      (is (= true (deref waiting 1000 :timeout)))
      (reset! continue? false)
      (is (= :cancelled (deref job 900 :timeout)))
      (is (= 1 @attempts))
      (finally (future-cancel job)))))

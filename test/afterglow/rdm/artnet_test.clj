(ns afterglow.rdm.artnet-test
  (:require [afterglow.rdm.artnet :as artnet]
            [afterglow.rdm.artnet.packets :as packet]
            [afterglow.rdm.transport :as transport]
            [clojure.test :refer [deftest is]])
  (:import [java.net DatagramPacket DatagramSocket InetAddress SocketException SocketTimeoutException]))

(def controller "7a70:01020304")

(def device "1234:abcdef01")

(def command {:universe 4661 :uid device :command :set :sub-device 4 :pid 0xf0 :data [1 2]})

(def prefix [65 114 116 45 78 101 116 0 0])

(def address [0x12 0 0x34])

(defn- wire [values] (byte-array (map unchecked-byte values)))

(defn- word [n] [(quot n 256) (mod n 256)])

(defn- with-checksum [p]
  (into p (word (mod (reduce + 0xcc (drop 24 p)) 65536))))

(def get-header
  (vec (concat prefix [0x83 0 14 1] (repeat 8 0) address)))

(defn- reply [msg {:keys [type class pid sub data tx] :or {type 0 data []}}]
  (with-checksum
    (vec (concat (take 24 msg) [1 (+ 24 (count data))]
                 (subvec msg 32 38) (subvec msg 26 32)
                 [(or tx (msg 38)) type 0] (or sub (subvec msg 41 43))
                 [(or class (inc (msg 43)))] (or pid (subvec msg 44 46))
                 [(count data)] data))))

(defn- tod [total block serials]
  (vec (concat prefix [0x81 0 14 1 2] (repeat 6 0) [3] address
               (word total) [block (count serials)]
               (mapcat #(into [0x12 0x34 0 0] (word %)) serials))))

(defn- receive [^DatagramSocket server]
  (let [buffer (byte-array 1500)
        datagram (DatagramPacket. buffer (alength buffer))]
    (.receive server datagram)
    [(mapv #(bit-and 255 (aget buffer %)) (range (.getLength datagram)))
     (.getSocketAddress datagram)]))

(defn- send-to [^DatagramSocket server address values]
  (let [data (wire values)]
    (.send server (DatagramPacket. data (alength data) address))))

(defn- with-node
  "Run both ends of an ephemeral, loopback-only exchange. Surface peer failures."
  [options simulate run]
  (with-open [server (DatagramSocket. 0 (InetAddress/getByName "127.0.0.1"))]
    (.setSoTimeout server 4000)
    (let [config (merge {:transport :art-net :host "127.0.0.1" :port (.getLocalPort server)
                         :local-port 0 :timeout-ms 1000 :controller-uid controller
                         :bind-index 3 :physical-port 2} options)
          deadline (+ (System/nanoTime) 5000000000)
          connection (transport/open! config deadline (fn [_]))
          node (future (simulate server))]
      (try
        (let [result (run connection deadline)]
          @node
          result)
        (finally ((:close! connection)) (future-cancel node))))))

(deftest published-layout-and-boundaries
  (is (= (into (vec (concat prefix [0x80 0 14] (repeat 9 0) [0x12 0 1 0x34])) (repeat 31 0))
         (packet/discovery-packet 4661 false)))
  (is (= (vec (concat prefix [0x82 0 14] (repeat 9 0) [127 1 255]))
         (packet/discovery-packet 32768 true)))
  (let [expected (vec (concat get-header [1 26 0x12 0x34 0xab 0xcd 0xef 1
                                         0x7a 0x70 1 2 3 4 42 1 0 0 4 0x30 0 0xf0 2 1 2]))]
    (is (= (with-checksum expected) (packet/command-packet controller 42 command)))
    (let [ok (reply (packet/command-packet controller 42 command) {})]
      (is (= {:response-code 0 :response-type 0 :message-count 0 :pid 240 :sub-device 4
              :command-class 1 :source-uid device :data []}
             (packet/read-response ok controller 42 command)))
      (doseq [invalid [(update ok (dec (count ok)) bit-xor 1) (assoc ok 25 0) (conj ok 0)]]
        (is (thrown? clojure.lang.ExceptionInfo (packet/read-response invalid controller 42 command))))))
  (doseq [u [0 32769]]
    (is (thrown? clojure.lang.ExceptionInfo (packet/discovery-packet u false))))
  (doseq [uid ["ffff:ffffffff" "1234:ffffffff" "ffff:12345678" "0000:00000000" controller]]
    (is (thrown? clojure.lang.ExceptionInfo (packet/command-packet controller 0 (assoc command :uid uid))))))

(deftest cached-discovery-assembles-only-the-selected-gateway-port
  (let [result (with-node {}
                 (fn [server]
                   (let [[request destination] (receive server)
                         first-block (tod 201 0 (range 200))
                         last-block (tod 201 1 [200])]
                     (is (= 0x80 (request 9)))
                     (doseq [block [(assoc last-block 23 0) (assoc last-block 20 0)
                                    (assoc last-block 13 1) last-block last-block first-block]]
                       (send-to server destination block))))
                 (fn [{:keys [request!]} _] (request! "GetUIDs" {:universe 4661})))]
    (is (= 4661 (:universe result)))
    (is (= (mapv #(format "1234:%08x" %) (range 201)) (:uids result)))))

(deftest discovery-retries-the-table-read-without-restarting-physical-discovery
  (let [result (with-node {:timeout-ms 250}
                 (fn [server]
                   (let [[flush destination] (receive server)]
                     (is (= 0x82 (flush 9)))
                     (send-to server destination (assoc (tod 0 0 []) 22 255))
                     (let [[request _] (receive server)]
                       (is (= 0x80 (request 9)))
                       (send-to server destination (tod 0 0 [])))))
                 (fn [{:keys [request!]} _] (request! "ForceDiscovery" {:universe 4661 :full? true})))]
    (is (= {:universe 4661 :uids []} result))))

(deftest discovery-inconsistencies-must-not-replace-the-rig-inventory
  (let [decode #(packet/read-tod % 4661 3 2)
        partial (packet/add-block {} (decode (tod 2 0 [1])))]
    (doseq [bad [(tod 513 0 []) (assoc (tod 2 0 [1]) 27 2)
                 (conj (tod 1 0 [1]) 0) (tod 0 1 [])]]
      (is (thrown? clojure.lang.ExceptionInfo (decode bad))))
    (doseq [bad [(tod 2 0 [2]) (tod 2 1 [1]) (tod 3 1 [2]) (tod 2 2 [2])]]
      (is (thrown? clojure.lang.ExceptionInfo (packet/add-block partial (decode bad)))))))

(defn- run-command [req]
  (fn [{:keys [request!]} deadline] (transport/command! request! req deadline (constantly true))))

(deftest delayed-set-ignores-stale-messages-and-reads-the-queue
  (let [result (with-node {}
                 (fn [server]
                   (let [[msg dst] (receive server)
                         ok (reply msg {:type 1 :data [0 0]})]
                     (is (= 0x30 (msg 43)))
                     (doseq [wrong [(assoc ok 32 0) (assoc ok 26 0) (assoc ok 23 0)
                                    (assoc ok 42 2) (assoc ok 43 0x21) (assoc ok 45 0xe0)
                                    (reply msg {:tx (mod (inc (msg 38)) 256)}) msg]]
                       (send-to server dst wrong))
                     (send-to server dst ok)
                     (let [[queued _] (receive server)]
                       (is (= [0 0 0x20 0 0x20 1 1] (subvec queued 41 48)))
                       (is (not= (msg 38) (queued 38)))
                       (send-to server dst (reply queued {:class 0x31 :pid [0 0xf0] :sub [0 4]})))))
                 (run-command command))]
    (is (= :ack (:status result)))
    (is (= 1 (:command-class result)))))

(deftest overflow-get-assembles-multiple-transactions-and-nack-survives
  (let [get-pids (assoc command :command :get :pid 0x50 :data [])
        result (with-node {}
                 (fn [server]
                   (let [[msg dst] (receive server)]
                     (send-to server dst (reply msg {:type 3 :data (vec (range 231))}))
                     (let [[next-msg _] (receive server)]
                       (is (not= (msg 38) (next-msg 38)))
                       (is (= (subvec msg 41 47) (subvec next-msg 41 47)))
                       (send-to server dst (reply next-msg {:data [255]})))))
                 (run-command get-pids))]
    (is (= :ack (:status result)))
    (is (= (conj (vec (range 231)) 255) (:data result))))
  (let [result (with-node {}
                 (fn [server]
                   (let [[msg dst] (receive server)]
                     (send-to server dst (reply msg {:type 2 :data [0 4]}))))
                 (run-command command))]
    (is (= [:nack :write-protect] ((juxt :status :reason) result)))))

(deftest timed-out-set-is-sent-once
  (with-node {:timeout-ms 100}
    (fn [^DatagramSocket server]
      (let [[msg _] (receive server)]
        (is (= 0x30 (msg 43)))
        (.setSoTimeout server 250)
        (is (thrown? SocketTimeoutException (receive server)))))
    (fn [connection deadline]
      (is (thrown? SocketTimeoutException ((run-command command) connection deadline))))))

(deftest close-interrupts-a-blocked-discovery
  (let [arrived (promise)]
    (with-node {}
      (fn [server] (receive server) (deliver arrived true))
      (fn [{:keys [request! close!]} _]
        (let [reader (future (try (request! "GetUIDs" {:universe 1})
                                  (catch SocketException _ :closed)))]
          (is (= true (deref arrived 1500 nil)))
          (close!)
          (is (= :closed (deref reader 1000 :blocked))))))))

(deftest invalid-configurations-do-not-start-discovery-or-send-a-command
  (is (= {:port 6454 :local-port 6454 :timeout-ms 3000 :bind-index 1 :physical-port 1
          :host "127.0.0.1" :controller-uid controller}
         (artnet/configuration {:host "127.0.0.1" :controller-uid "7A70:01020304"})))
  (doseq [config [{:host "not-an-address"} {:host "999.0.0.1"} {:host "0.0.0.0"}
                  {:host "239.0.0.1"} {:host "255.255.255.255"} {:port 0}
                  {:local-port -1} {:timeout-ms 0} {:physical-port 0}
                  {:physical-port 5} {:bind-index 256} {:bind-host "::1"} {:controller-uid "1234:ffffffff"}]]
    (is (thrown? clojure.lang.ExceptionInfo
                 (transport/open! (merge {:transport :art-net :host "127.0.0.1" :local-port 0} config)
                                  (+ (System/nanoTime) 1000000000) (fn [_]))))))

(deftest an-overflow-reply-cannot-repeat-a-set
  (with-node {}
    (fn [^DatagramSocket server]
      (let [[request dst] (receive server)]
        (send-to server dst (reply request {:type 3 :data [1]}))
        (.setSoTimeout server 200)
        (is (thrown? SocketTimeoutException (receive server)))))
    (fn [connection deadline]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"overflow continuation"
                            ((run-command command) connection deadline))))))

(deftest explicit-full-discovery-and-individual-controller-uid-required
  (with-node {:controller-uid nil}
    (fn [^DatagramSocket server]
      (.setSoTimeout server 250)
      (is (thrown? SocketTimeoutException (receive server))))
    (fn [{:keys [request!] :as connection} deadline]
      (is (thrown? clojure.lang.ExceptionInfo
                   (request! "ForceDiscovery" {:universe 1 :full? "false"})))
      (is (thrown? clojure.lang.ExceptionInfo ((run-command command) connection deadline))))))

(deftest a-reused-session-discards-queued-tod-before-flushing-the-gateway
  (let [duplicate-sent (promise)]
    (with-node {}
      (fn [server]
        (let [[_ dst] (receive server)
              old-table (tod 1 0 [1])]
          (send-to server dst old-table)
          (send-to server dst old-table)
          (deliver duplicate-sent true)
          (let [[flush _] (receive server)]
            (is (= 0x82 (flush 9)))
            (send-to server dst (tod 1 0 [2])))))
      (fn [{:keys [request!]} _]
        (is (= ["1234:00000001"] (:uids (request! "GetUIDs" {:universe 4661}))))
        (is (= true (deref duplicate-sent 1000 nil)))
        (is (= ["1234:00000002"] (:uids (request! "ForceDiscovery" {:universe 4661 :full? true}))))))))

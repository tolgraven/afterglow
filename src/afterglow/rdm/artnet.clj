(ns afterglow.rdm.artnet
  "One cancellable Art-Net 4 RDM session with an explicitly selected output gateway."
  (:require [afterglow.rdm.artnet.packets :as packet]
            [afterglow.rdm.codec :as rdm]
            [afterglow.rdm.deadline :as deadline]
            [clojure.string :as str])
  (:import [java.net DatagramPacket DatagramSocket InetAddress InetSocketAddress SocketTimeoutException]
           [java.util.concurrent ThreadLocalRandom]
           [java.util.concurrent.atomic AtomicInteger]))

;; Advance across job socket lifetimes so a previous job's late reply will
;; normally carry a different transaction number, even on the same UDP port.
(defonce ^:private ^AtomicInteger transaction-sequence
  (AtomicInteger. (.nextInt (ThreadLocalRandom/current) 256)))

(defn- send! [^DatagramSocket socket octets deadline]
  (deadline/remaining-ms deadline)
  (let [data (byte-array (map unchecked-byte octets))]
    (.send socket (DatagramPacket. data (alength data)))))

(defn- receive! [^DatagramSocket socket deadline decode]
  (let [buffer (byte-array 1500)
        datagram (DatagramPacket. buffer (alength buffer))]
    (loop []
      (.setSoTimeout socket (int (min Integer/MAX_VALUE (deadline/remaining-ms deadline))))
      (.setLength datagram (alength buffer))
      (.receive socket datagram)
      (let [bytes (mapv #(bit-and 255 (aget buffer %)) (range (.getLength datagram)))]
        (or (decode bytes) (recur))))))

(defn- response-deadline [deadline timeout-ms]
  (min deadline (+ (System/nanoTime) (* 1000000 (long timeout-ms)))))

(defn- discard-pending! [^DatagramSocket socket deadline]
  ;; ArtTodData has no transaction number. On a reused session a duplicate table
  ;; may still be queued from the last discovery on this same physical port.
  (let [discard (DatagramPacket. (byte-array 1) 1)]
    (.setSoTimeout socket 1)
    (loop []
      (deadline/remaining-ms deadline)
      (when (try (.receive socket discard) true (catch SocketTimeoutException _ false))
        (recur)))))

(defn- discover! [socket {:keys [bind-index physical-port timeout-ms]} deadline universe full?]
  (when-not (or (nil? full?) (boolean? full?))
    (rdm/fail! "Full discovery requires an explicit boolean" {:full? full?}))
  (let [cached-request (packet/discovery-packet universe false)
        decode #(packet/read-tod % universe bind-index physical-port)]
    (discard-pending! socket deadline)
    (send! socket (if full? (packet/discovery-packet universe true) cached-request) deadline)
    (loop [table {} attempt 0 window (response-deadline deadline timeout-ms)]
      (let [block (try (receive! socket window decode) (catch SocketTimeoutException _ :timeout))]
        (case block
          ;; A gateway can send TodNak during physical discovery. It will send
          ;; its complete table when ready. Never restart a running discovery.
          :incomplete (recur {} attempt window)
          :timeout (do
                     (deadline/remaining-ms deadline)
                     (when (>= attempt 2)
                       (throw (SocketTimeoutException. "No complete ArtTodData table from the selected gateway port")))
                     (send! socket cached-request deadline)
                     ;; A flush may trigger a lengthy scan. After the last cached
                     ;; read, give the gateway the rest of the job to announce its ToD.
                     (recur {} (inc attempt) (if (and full? (= 1 attempt))
                                              deadline (response-deadline deadline timeout-ms))))
          (let [{:keys [uids] :as assembled} (packet/add-block table block)]
            (if uids {:universe universe :uids uids} (recur assembled attempt window))))))))

(defn- exchange! [socket controller request deadline]
  (let [tx (bit-and 255 (.getAndIncrement transaction-sequence))]
    (send! socket (packet/command-packet controller tx request) deadline)
    (receive! socket deadline #(packet/read-response % controller tx request))))

(defn- assemble-reply [reply! request]
  (loop [data [] previous nil fragments 0]
    (let [{:keys [response-type] :as reply} (reply!)
          responder (select-keys reply [:source-uid :command-class :pid :sub-device])
          assembled (into data (:data reply))]
      (when (and previous (or (not= previous responder) (not (#{0 3} response-type))))
        (rdm/fail! "RDM continuation did not complete the same parameter response" {:received responder}))
      (when (> (count assembled) 65536)
        (rdm/fail! "RDM overflow response exceeds 64 KiB" {}))
      (if (= 3 response-type)
        (do
          (when (or (not= :get (:command request)) (>= fragments 511) (empty? (:data reply)))
            (rdm/fail! "Invalid or unbounded RDM overflow continuation" {:pid (:pid request)}))
          (recur assembled responder (inc fragments)))
        (assoc reply :data assembled)))))

(defn- command! [socket {:keys [controller-uid timeout-ms]} deadline request]
  (let [request (rdm/validate-command request)
        controller (rdm/uid controller-uid)
        reply! #(exchange! socket controller request (response-deadline deadline timeout-ms))]
    (assemble-reply reply! request)))

(defn- request! [socket config deadline method {:keys [universe full?] :as request}]
  (case method
    "ForceDiscovery" (discover! socket config deadline universe full?)
    "GetUIDs" (discover! socket config deadline universe false)
    "RDMCommand" (command! socket config deadline request)
    (rdm/fail! "Unsupported Art-Net RDM operation" {:method method})))

(defn- ipv4 [host]
  ;; Literal addresses also keep DNS resolution out of a cancellable job.
  (let [parts (when (and (string? host) (re-matches #"[0-9]{1,3}(?:\.[0-9]{1,3}){3}" host))
                (mapv parse-long (str/split host #"\.")))]
    (when-not (and parts (every? #(rdm/uint? 8 %) parts))
      (rdm/fail! "Art-Net RDM requires an IPv4 address" {:host host}))
    (InetAddress/getByAddress (byte-array (map unchecked-byte parts)))))

(defn- endpoint [host port]
  (let [^InetAddress ip (ipv4 host)
        first-octet (bit-and 255 (aget (.getAddress ip) 0))]
    (when-not (and (<= 1 first-octet 223) (rdm/uint? 16 port) (pos? port))
      (rdm/fail! "Art-Net RDM requires an IPv4 unicast gateway and UDP port" {:host host :port port}))
    (InetSocketAddress. ip (int port))))

(defn configuration
  "Check session settings without binding a socket or contacting a gateway."
  [options]
  (let [{:keys [host port bind-host local-port controller-uid timeout-ms bind-index physical-port] :as config}
        (merge {:port 6454 :local-port 6454 :timeout-ms 3000 :bind-index 1 :physical-port 1} options)]
    (when-not (and (rdm/uint? 16 local-port) (integer? timeout-ms) (<= 1 timeout-ms Integer/MAX_VALUE)
                   (rdm/uint? 8 bind-index) (integer? physical-port) (<= 1 physical-port 4))
      (rdm/fail! "Invalid Art-Net RDM local port, timeout or physical port selection" {}))
    (endpoint host port)
    (when bind-host (ipv4 bind-host))
    (cond-> (select-keys config [:host :port :bind-host :local-port :timeout-ms :bind-index :physical-port])
      controller-uid (assoc :controller-uid (packet/individual-uid controller-uid)))))

(defn open!
  "Bind one job-owned UDP socket. Configure an individual controller UID for GET/SET.
  The host selects the responding ArtTodData BindIndex and Port (each defaults to 1)."
  [options deadline register!]
  (let [{:keys [host port bind-host local-port] :as config} (configuration options)]
    (let [socket (DatagramSocket. nil)]
      (try
        (register! #(.close socket))
        (let [gateway (endpoint host port)
              local (if bind-host (InetSocketAddress. ^InetAddress (ipv4 bind-host) (int local-port))
                        (InetSocketAddress. (int local-port)))]
          (deadline/remaining-ms deadline)
          (.setBroadcast socket false)
          (.bind socket local)
          (.connect socket ^InetSocketAddress gateway)
          {:close! #(.close socket)
           :request! (partial request! socket config deadline)})
        (catch Throwable e (.close socket) (throw e))))))

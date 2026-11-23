(ns afterglow.rdm.ola
  "OLA's job-owned RDM RPC connection."
  (:require [afterglow.rdm.codec :as codec]
            [afterglow.rdm.deadline :as deadline])
  (:import [java.io EOFException]
           [java.net InetSocketAddress Socket]))

(defn- read-exactly! [^Socket socket deadline timeout-ms size]
  (let [buffer (byte-array size)
        stream (.getInputStream socket)]
    (loop [offset 0]
      (if (= offset size)
        buffer
        (do
          (.setSoTimeout socket (int (min timeout-ms (deadline/remaining-ms deadline))))
          (let [n (.read stream buffer offset (- size offset))]
            (when (neg? n) (throw (EOFException. "OLA closed the RDM connection")))
            (recur (+ offset n))))))))

(defn- request! [^Socket socket deadline timeout-ms sequence method request]
  (let [id (vswap! sequence inc)
        data (codec/rpc-packet id method request)
        stream (.getOutputStream socket)]
    (deadline/remaining-ms deadline)
    (.write stream ^bytes data)
    (.flush stream)
    (let [size (codec/message-size (read-exactly! socket deadline timeout-ms 4))
          reply (read-exactly! socket deadline timeout-ms size)]
      (codec/decode-reply id method request (mapv #(bit-and 255 %) reply)))))

(defn open!
  "Register cancellation before connecting. The owner closes the socket at its deadline."
  [{:keys [host port timeout-ms]} deadline register!]
  (let [socket (Socket.)]
    (try
      (register! #(.close socket))
      (.connect socket (InetSocketAddress. ^String host (int port))
                (int (min timeout-ms (deadline/remaining-ms deadline))))
      (.setTcpNoDelay socket true)
      {:close! #(.close socket)
       :request! (partial request! socket deadline timeout-ms (volatile! 0))}
      (catch Throwable error (.close socket) (throw error)))))

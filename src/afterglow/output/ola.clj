(ns afterglow.output.ola
  "DMX output over an explicitly owned olad streaming RPC connection."
  (:import [java.io ByteArrayOutputStream IOException]
           [java.net InetSocketAddress SocketTimeoutException]
           [java.nio ByteBuffer ByteOrder]
           [java.nio.channels SocketChannel Selector SelectionKey]
           [java.util.concurrent.atomic AtomicBoolean]))

(def ^:private byte-array-class (class (byte-array 0)))

(defn- write-varint! [^ByteArrayOutputStream stream number]
  (loop [number (long number)]
    (if (< number 128)
      (.write stream (int number))
      (do (.write stream (int (bit-or 128 (bit-and number 127))))
          (recur (unsigned-bit-shift-right number 7))))))

(defn ola-stream-packet
  "Encode an owned OLA StreamDmxData RPC, including its native-endian framing.
  OLA universe IDs pass through unchanged (0..65535); request IDs are uint32.
  Unlike ArtDMX, DMX payloads may have any length from 1 to 512.
  This is the fixed write-only subset of OLA's Rpc.proto and Ola.proto; the output port is patched by olad."
  [universe request-id values]
  (let [bytes? (instance? byte-array-class values)
        n (if bytes? (alength ^bytes values) (count values))]
    (when-not (and (integer? universe) (<= 0 universe 65535)
                   (integer? request-id) (<= 0 request-id 4294967295)
                   (<= 1 n 512))
      (throw (ex-info "OLA needs universe 0..65535, uint32 request ID and 1..512 channels" {})))
    (let [dmx (ByteArrayOutputStream. (+ n 8))
          rpc (ByteArrayOutputStream. (+ n 40))
          method (.getBytes "StreamDmxData" java.nio.charset.StandardCharsets/US_ASCII)]
      (.write dmx 8) ; DmxData.universe, int32
      (write-varint! dmx universe)
      (.write dmx 18) ; DmxData.data, bytes
      (write-varint! dmx n)
      (if bytes?
        (.write dmx ^bytes values 0 n)
        (doseq [[index value] (map-indexed vector values)]
          (when-not (and (integer? value) (<= -128 value 255))
            (throw (ex-info "Invalid DMX byte" {:index index :value value})))
          (.write dmx (int (bit-and value 255)))))
      (.write rpc 8) ; RpcMessage.type = STREAM_REQUEST
      (.write rpc 10)
      (.write rpc 16) ; RpcMessage.id
      (write-varint! rpc request-id)
      (.write rpc 26) ; RpcMessage.name
      (write-varint! rpc (alength method))
      (.write rpc method 0 (alength method))
      (.write rpc 34) ; RpcMessage.buffer
      (write-varint! rpc (.size dmx))
      (.writeTo dmx rpc)
      (let [body (.toByteArray rpc)
            packet (byte-array (+ 4 (alength body)))]
        (-> (ByteBuffer/wrap packet) (.order (ByteOrder/nativeOrder))
            (.putInt (int (bit-or 0x10000000 (alength body)))))
        (System/arraycopy body 0 packet 4 (alength body))
        packet))))

(defn- await-ready! [^Selector selector deadline-nanos]
  (let [remaining (- deadline-nanos (System/nanoTime))]
    (when-not (pos? remaining)
      (throw (SocketTimeoutException. "OLA transport deadline exceeded")))
    ;; A zero select timeout would wait forever. Round positive fractions up.
    (.select selector (long (max 1 (Math/ceil (/ remaining 1000000.0)))))
    (.clear (.selectedKeys selector))))

(defn- open-ola-transport!
  [{:keys [host port connect-timeout-ms write-timeout-ms]}]
  (let [channel (SocketChannel/open)
        ^Selector selector (try (Selector/open)
                      (catch Throwable error
                        (try (.close channel) (catch Throwable cleanup (.addSuppressed error cleanup)))
                        (throw error)))
        close! (fn []
                 (.wakeup selector)
                 (try (.close channel) (finally (.close selector))))]
    (try
      (.configureBlocking channel false)
      (.setTcpNoDelay (.socket channel) true)
      (let [address (InetSocketAddress. ^String host (int port))
            key (.register channel selector SelectionKey/OP_CONNECT)
            deadline (+ (System/nanoTime) (* 1000000 (long connect-timeout-ms)))]
        (when-not (.connect channel address)
          (loop []
            (when-not (.finishConnect channel)
              (await-ready! selector deadline)
              (recur))))
        (.interestOps key SelectionKey/OP_WRITE))
      {:write! (fn [packets]
                 ;; Gathering writes avoid one syscall per universe. All bytes
                 ;; in one lighting frame share a single bounded write budget.
                 (let [^"[Ljava.nio.ByteBuffer;" buffers (into-array ByteBuffer (map #(ByteBuffer/wrap ^bytes %) packets))
                       deadline (+ (System/nanoTime) (* 1000000 (long write-timeout-ms)))]
                   (loop []
                     (when (some #(.hasRemaining ^ByteBuffer %) buffers)
                       (when-not (.isOpen channel) (throw (IOException. "OLA connection is closed")))
                       (when (<= deadline (System/nanoTime))
                         (throw (SocketTimeoutException. "OLA frame write deadline exceeded")))
                       (when (zero? (.write channel buffers))
                         (await-ready! selector deadline))
                       (recur)))))
       :close! close!}
      (catch Throwable error
        (try (close!) (catch Throwable cleanup (.addSuppressed error cleanup)))
        (throw error)))))

(defn open-ola!
  "Explicitly connect one sink to olad (default 127.0.0.1:9010).
  Sends StreamDmxData without per-universe acknowledgement. Success means local
  TCP write completion, not fixture delivery. Port patching belongs to olad.

  For testing, :open-transport! receives validated host/port/deadline options and
  returns {:write! (fn [vector-of-owned-packets]) :close! (fn [])}. A write must
  consume its packets synchronously and respect :write-timeout-ms. Closing must
  interrupt a pending write. A failed write closes the sink; reopening is explicit."
  [{:keys [host port connect-timeout-ms write-timeout-ms open-transport!]
    :or {host "127.0.0.1" port 9010 connect-timeout-ms 1000 write-timeout-ms 1000
         open-transport! open-ola-transport!}}]
  (when-not (and (string? host) (seq host) (integer? port) (<= 1 port 65535)
                 (integer? connect-timeout-ms) (<= 1 connect-timeout-ms 60000)
                 (integer? write-timeout-ms) (<= 1 write-timeout-ms 60000)
                 (ifn? open-transport!))
    (throw (ex-info "OLA requires a host, port 1..65535 and transport deadlines 1..60000ms" {})))
  (let [{:keys [write! close!]} (open-transport! {:host host :port port
                                                :connect-timeout-ms connect-timeout-ms
                                                :write-timeout-ms write-timeout-ms})
        closed? (AtomicBoolean. false)
        close-once! #(when (.compareAndSet closed? false true) (close!))
        write-lock (Object.)
        request-id (volatile! 0)]
    (when-not (and (ifn? write!) (ifn? close!))
      (when (ifn? close!) (close!))
      (throw (ex-info "OLA transport requires :write! and :close!" {})))
    {:send! (fn [universes _frame-number]
              (locking write-lock
                (when (.get closed?) (throw (IOException. "OLA sink is closed")))
                (when-not (map? universes)
                  (throw (ex-info "OLA frame must map universe IDs to DMX buffers" {})))
                (when-not (every? #(and (integer? %) (<= 0 % 65535)) (keys universes))
                  (throw (ex-info "OLA universe IDs must be integers in 0..65535" {})))
                ;; Validate every universe before sending any part of this frame.
                (let [packets (mapv (fn [index [universe values]]
                                      (ola-stream-packet universe
                                                         (bit-and 0xffffffff (+ @request-id index)) values))
                                    (range) (sort-by key universes))]
                  (when (seq packets)
                    (vswap! request-id #(bit-and 0xffffffff (+ % (count packets))))
                    (try (write! packets)
                         (catch Throwable error
                           ;; A partial TCP write cannot be resumed as a new RPC.
                           (try (close-once!) (catch Throwable cleanup (.addSuppressed error cleanup)))
                           (throw error)))))))
     :close! close-once!
     :description {:type :ola :host host :port port :method :stream-dmx-data}}))

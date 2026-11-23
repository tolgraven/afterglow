(ns afterglow.control.devices.transports
  "Optional real transports, acquired only through returned open! functions.
  Java MIDI uses explicit ports; OSC and Wayang are loaded lazily on acquisition."
  (:require [afterglow.control.params :as params]
            [clojure.string :as str])
  (:import [javax.sound.midi MidiSystem MidiDevice MidiMessage Receiver ShortMessage SysexMessage]
           [java.awt Color Font FontMetrics RenderingHints]
           [java.awt.image BufferedImage]
           [java.math BigDecimal]
           [java.util Locale]
           [java.util.concurrent Callable ExecutionException Executors FutureTask ThreadFactory TimeUnit TimeoutException]))

(defn scheduler
  "Return an explicit session scheduler factory. Each acquisition owns one daemon
  worker and returns cancellation; no executor exists until the factory is called."
  [interval-ms]
  (when-not (and (integer? interval-ms) (<= 10 interval-ms 10000))
    (throw (ex-info "UI refresh interval must be between 10 and 10000 milliseconds" {})))
  (fn [refresh!]
    (let [executor (Executors/newSingleThreadScheduledExecutor
                    (reify ThreadFactory
                      (newThread [_ task] (doto (Thread. task "afterglow-device-feedback") (.setDaemon true)))))
          task (.scheduleWithFixedDelay executor
                 ^Runnable (fn [] (try (refresh!) (catch Exception _)))
                 (long interval-ms) (long interval-ms) TimeUnit/MILLISECONDS)]
      (fn [] (.cancel task false) (.shutdown executor)))))

(defn- enumerate-midi-ports
  []
  (mapv (fn [index info]
          (let [device (MidiSystem/getMidiDevice info)]
            {:index index :name (.getName info) :description (.getDescription info)
             :vendor (.getVendor info) :version (.getVersion info)
             :input? (not (zero? (.getMaxTransmitters device)))
             :output? (not (zero? (.getMaxReceivers device)))}))
        (range) (MidiSystem/getMidiDeviceInfo)))

(defn- port-scanner [enumerate! wait-ms]
  (let [active (atom nil)
        scan (fn []
               (let [task (FutureTask. ^Callable enumerate!)
                     thread (doto (Thread. task "afterglow-midi-discovery") (.setDaemon true))]
                 (.start thread)
                 (reset! active task)))]
    (fn []
      (let [^FutureTask task (locking active (or @active (scan)))]
        (try
          (let [ports (.get task (long wait-ms) TimeUnit/MILLISECONDS)]
            (compare-and-set! active task nil)
            ports)
          (catch ExecutionException error
            (compare-and-set! active task nil)
            (throw (.getCause error)))
          (catch TimeoutException error
            ;; Native drivers may ignore interruption. A retry joins the same scan.
            (throw (ex-info "MIDI device discovery is still running. Refresh devices to check again."
                            {:reason :midi/discovery-pending} error))))))))

;; The native MIDI system belongs to the process. A namespace reload may update
;; enumeration, but must join a provider call that is already in progress.
(defonce ^:private scan-midi-ports (port-scanner #'enumerate-midi-ports 1500))

(defn midi-ports
  "List current JVM MIDI ports without opening devices. Concurrent callers share one
  daemon scan. A slow driver returns a retryable discovery-pending error in 1.5 s.
  Refreshing can collect its result even if the original caller timed out."
  []
  (scan-midi-ports))

(defn- midi-message [data]
  (let [bytes (mapv #(do (when-not (and (integer? %) (<= 0 % 255))
                          (throw (ex-info "MIDI bytes must be unsigned integers" {:value %}))) %) data)]
    (when-not (seq bytes) (throw (ex-info "Empty MIDI message" {})))
    (if (= 0xf0 (first bytes))
      (doto (SysexMessage.) (.setMessage (byte-array (map unchecked-byte bytes)) (count bytes)))
      (let [[status a b] bytes]
        (when-not (<= 1 (count bytes) 3) (throw (ex-info "Invalid short MIDI message length" {})))
        (doto (ShortMessage.) (.setMessage status (or a 0) (or b 0)))))))

(defn midi-transport
  "Create a transport for explicitly selected indices from midi-ports. Optional
  expected names detect changed OS enumeration. Existing open devices remain
  open; only this transport's transmitter/receiver and owned devices are closed.
  batch-pause-ms limits long palette restoration bursts; ordinary LED updates
  are additionally acknowledged in the Push 2 profile."
  [{:keys [input-index output-index expected-input-name expected-output-name batch-size batch-pause-ms]
    :or {batch-size 10 batch-pause-ms 5}}]
  (when-not (and (every? #(and (integer? %) (<= 0 %)) [input-index output-index])
                 (integer? batch-size) (pos? batch-size)
                 (integer? batch-pause-ms) (<= 0 batch-pause-ms 100))
    (throw (ex-info "Explicit input/output indices and valid batch options are required" {})))
  {:open!
   (fn [receive!]
     (let [infos (vec (MidiSystem/getMidiDeviceInfo))
           input-info (get infos input-index)
           output-info (get infos output-index)
           _ (when-not (and input-info output-info)
               (throw (ex-info "Selected MIDI port no longer exists" {})))
           _ (doseq [[info expected] [[input-info expected-input-name] [output-info expected-output-name]]]
               (when (and expected (not= expected (.getName info)))
                 (throw (ex-info "MIDI port name changed; reselect the intended port" {:expected expected :actual (.getName info)}))))
           input (MidiSystem/getMidiDevice input-info)
           output (if (= input-index output-index) input (MidiSystem/getMidiDevice output-info))
           owned (atom []) resources (atom {})]
       (try
         (doseq [^MidiDevice device (distinct [input output])]
           (when-not (.isOpen device) (.open device) (swap! owned conj device)))
         (let [receiver (.getReceiver ^MidiDevice output)]
           (swap! resources assoc :receiver receiver))
         (let [transmitter (.getTransmitter ^MidiDevice input)]
           (swap! resources assoc :transmitter transmitter)
           (.setReceiver transmitter
             (reify Receiver
               (send [_ message _timestamp]
                 (receive! (mapv #(bit-and 0xff %) (take (.getLength ^MidiMessage message) (.getMessage ^MidiMessage message)))))
               (close [_] nil))))
         (assoc @resources :owned-devices @owned)
         (catch Exception error
           (doseq [resource (vals @resources)] (try (.close ^java.lang.AutoCloseable resource) (catch Exception _)))
           (doseq [^MidiDevice device @owned] (try (.close device) (catch Exception _)))
           (throw error)))))
   :send!
   (fn [{:keys [receiver]} messages]
     (doseq [[index message] (map-indexed vector messages)]
       (.send ^Receiver receiver (midi-message message) -1)
       (when (and (pos? batch-pause-ms) (zero? (mod (inc index) batch-size)) (< (inc index) (count messages)))
         (Thread/sleep batch-pause-ms))))
   :close!
   (fn [{:keys [transmitter receiver owned-devices]}]
     (doseq [resource [transmitter receiver]]
       (when resource (try (.close ^java.lang.AutoCloseable resource) (catch Exception _))))
     (doseq [^MidiDevice device owned-devices] (.close device)))})

(defn osc-transport
  "Open an OSC command listener without advertising it over Zeroconf. :port-in
  (or :port) may be zero. Optional :address and :port-out configure feedback."
  [{:keys [port port-in port-out address bind-host] :or {address "127.0.0.1"}}]
  (let [port (or port-in port)]
    (when-not (and (integer? port) (<= 0 port 65535)
                   (or (nil? port-out) (and (integer? port-out) (<= 1 port-out 65535))))
      (throw (ex-info "Invalid OSC input or output port" {})))
    {:open!
     (fn [receive!]
       (let [new-peer (requiring-resolve 'overtone.osc/osc-peer)
             listen! (requiring-resolve 'overtone.osc/osc-listen)
             close! (requiring-resolve 'overtone.osc/osc-close)
             send! (requiring-resolve 'overtone.osc/osc-send)
             destination (when port-out (java.net.InetSocketAddress. ^String address (int port-out)))
             local (if bind-host (java.net.InetSocketAddress. ^String bind-host (int port))
                       (java.net.InetSocketAddress. (int port)))
             peer (cond-> (new-peer true true) destination (assoc :addr (ref destination)))
             socket (.socket ^java.nio.channels.DatagramChannel (:chan peer))]
         (try
           ;; osc-server requires a service name. A bound generic peer uses the
           ;; same bundle-aware decoder without registering a discovery service.
           (listen! peer #(receive! {:path (:path %) :args (vec (:args %))}) ::controller)
           (.bind socket local)
           {:port (.getLocalPort socket) :peer peer :close! close!
            :feedback! (when destination (fn [path args] (apply send! peer path args)))}
           (catch Throwable failure
             ;; The library listener waits for a successful bind before reading.
             (when-not (.isBound socket) (.interrupt ^Thread (:listen-thread peer)))
             (close! peer)
             (throw failure)))))
     :send! (fn [handle messages]
              (when-let [feedback! (:feedback! handle)]
                (doseq [{:keys [path args]} messages] (feedback! path args))))
     :close! (fn [{:keys [peer close!]}] (close! peer))}))

(defn- parameter-value-label [^FontMetrics metrics value available-width]
  (let [text (str value)
        fits? #(<= (.stringWidth metrics ^String %) available-width)]
    (if-not (params/finite-number? value)
      (subs text 0 (min 12 (count text)))
      (let [^BigDecimal number (bigdec (if (ratio? value) (double value) value))
            significant-digits 6]
        (if (and (fits? text) (or (integer? value) (ratio? value)
                                 (<= (.precision number) significant-digits)))
          text
          (or (some (fn [digits]
                      (let [label (String/format Locale/ROOT (str "%." digits "g") (object-array [number]))
                            [mantissa exponent] (str/split label #"e" 2)
                            mantissa (if (str/includes? mantissa ".")
                                       (str/replace mantissa #"\.?0+$" "")
                                       mantissa)
                            label (if exponent (str mantissa "e" exponent) mantissa)]
                        (if (fits? label)
                          label
                          (when exponent
                            (let [shorter (str mantissa "e" (Long/parseLong exponent))]
                              (when (fits? shorter) shorter))))))
                    (range significant-digits 0 -1))
              (when (fits? "…") "…")
              ""))))))

(defn render-view!
  "Render a shared Push display view into an owned BufferedImage. This AWT
  boundary is independently testable headlessly; it does not send a frame."
  [^BufferedImage image view]
  (let [graphics (.createGraphics image)
        width (.getWidth image) height (.getHeight image)
        cell (quot width 8)]
    (try
      (.setRenderingHint graphics RenderingHints/KEY_TEXT_ANTIALIASING RenderingHints/VALUE_TEXT_ANTIALIAS_ON)
      (.setColor graphics (Color. 9 12 18)) (.fillRect graphics 0 0 width height)
      (.setFont graphics (Font. "SansSerif" Font/BOLD 18)) (.setColor graphics (Color. 235 240 246))
      (.drawString graphics (str (:title view) "  " (:page view) "  " (:status view)) 16 28)
      (.setFont graphics (Font. "SansSerif" Font/PLAIN 14))
      (.drawString graphics (str "BPM " (:bpm view) "  Master " (:master view)
                                 (when (= {:target :tempo :editable? false} (:touched-control view)) "  Tempo locked to sync")
                                 (when (:blackout? view) "  BLACKOUT")
                                 (when (:fine? view) "  Fine")) 16 52)
      (let [metrics (.getFontMetrics graphics)
            available-width (max 0 (- cell 16))]
        (doseq [[index {:keys [name value]}] (map-indexed vector (take 8 (:parameters view)))]
          (.setColor graphics (Color. 105 192 236))
          (.drawString graphics (subs (str name) 0 (min 12 (count (str name)))) (+ 8 (* cell index)) 88)
          (.setColor graphics Color/WHITE)
          (.drawString graphics ^String (parameter-value-label metrics value available-width) (+ 8 (* cell index)) 112)))
      (doseq [[index label] (map-indexed vector (take 8 (:labels view)))]
        (.setColor graphics (Color. 160 170 184))
        (.drawString graphics (subs (str label) 0 (min 12 (count (str label)))) (+ 8 (* cell index)) (- height 15)))
      image
      (finally (.dispose graphics)))))

(defonce ^:private wayang-owner (atom nil))

(defn- native-wayang []
  {:open! #(clojure.lang.Reflector/invokeStaticMethod "org.deepsymmetry.Wayang" "open" (object-array 0))
   :send! #(clojure.lang.Reflector/invokeStaticMethod "org.deepsymmetry.Wayang" "sendFrame" (object-array 0))
   :close! #(clojure.lang.Reflector/invokeStaticMethod "org.deepsymmetry.Wayang" "close" (object-array 0))})

(defn wayang-display
  "Lazy native display adapter. Wayang exposes a process-global display, so this
  wrapper grants one exclusive lease and refuses a second open. Inject :backend
  only for tests/alternate native implementations; real hardware is never opened
  until open!. Independent MIDI sessions can use separate non-Wayang displays."
  ([] (wayang-display {}))
  ([{:keys [backend renderer!] :or {renderer! render-view!}}]
   (when-not (ifn? renderer!) (throw (ex-info "Display renderer must be callable" {})))
   (let [backend (or backend (native-wayang)) token (Object.)]
     {:open! (fn []
               (locking wayang-owner
                 (when @wayang-owner (throw (ex-info "Wayang display is already owned by another session" {})))
                 (let [image ((:open! backend))]
                   (when-not (instance? BufferedImage image)
                     (try ((:close! backend)) (catch Exception _))
                     (throw (ex-info "Wayang did not return a BufferedImage" {})))
                   (reset! wayang-owner token)
                   {:image image :token token})))
      :render! (fn [{:keys [image token]} view]
                 (locking wayang-owner
                   (when-not (identical? token @wayang-owner)
                     (throw (ex-info "Display lease is no longer active" {})))
                   (renderer! image view)
                   ((:send! backend))))
      :close! (fn [{:keys [token]}]
                (locking wayang-owner
                  (when (identical? token @wayang-owner)
                    (try ((:close! backend)) (finally (reset! wayang-owner nil))))))})))

(ns afterglow.sync.beat-link
  "Pro DJ Link discovery, clocks and optional VirtualCdj status."
  (:require [clojure.string :as str]
            [afterglow.sync.peer :as pairing]
            [afterglow.time :refer [finite-number?] :rename {finite-number? finite?}]
            [afterglow.sync.session :refer [apply-clock! emit! fail!]])
  (:import [java.lang.reflect Proxy InvocationHandler]))

(defn announcement-data
  "Read real Beat Link announcement getters into portable peer data. Announcement
  timestamps are wall-clock milliseconds, so the host supplies observation time."
  [announcement observed-at-ms]
  {:device-number (.getDeviceNumber announcement) :device-name (.getDeviceName announcement)
   :address (.getHostAddress (.getAddress announcement))
   :hardware-address (str/join ":" (map #(format "%02x" (bit-and 255 %)) (.getHardwareAddress announcement)))
   :observed-at-ms observed-at-ms})

(defn beat-data
  "Read Beat Link 8 Beat getters. DeviceUpdate.getTimestamp is nanoTime, unlike
  DeviceAnnouncement; convert its age into the explicit host logical domain.
  Player-number bar significance is labeled heuristic until status is available."
  [beat observed-at-ms observed-nanos]
  (let [age (max 0.0 (/ (- observed-nanos (.getTimestamp beat)) 1000000.0))
        bpm (.getEffectiveTempo beat) number (.getDeviceNumber beat)]
    {:type :beat-link/beat :time-ms (max 0.0 (- observed-at-ms age)) :received-at-ms observed-at-ms :packet-age-ms age
     :bpm (when (and (not= 65535 (.getBpm beat)) (finite? bpm) (pos? bpm)) bpm)
     :beat-within-bar (.getBeatWithinBar beat) :bar-meaningful? (< number 33)
     :bar-meaning-source :player-number-heuristic
     :peer {:device-number number :device-name (.getDeviceName beat) :address (.getHostAddress (.getAddress beat))}}))

(defonce ^:private beatlink-lease (atom nil))

(defn- singleton [class-name] (clojure.lang.Reflector/invokeStaticMethod class-name "getInstance" (object-array 0)))

(defn- listener [class-name methods]
  (let [interface (Class/forName class-name)]
    (Proxy/newProxyInstance (.getClassLoader interface) (into-array Class [interface])
      (reify InvocationHandler
        (invoke [_ proxy method arguments]
          (case (.getName method)
            "hashCode" (System/identityHashCode proxy) "equals" (identical? proxy (aget arguments 0)) "toString" class-name
            (when-let [handler (get methods (.getName method))] (apply handler (seq arguments)))))))))

(defn transport
  "Explicit Beat Link 8 adapter. Listener registration and socket acquisition
  happen only in open!. Owns an exclusive lease on the library singletons and
  refuses to stop/share components owned by another integration. Optional status
  mode starts VirtualCdj (network announcements); default is passive beat/device
  reception. Never requires afterglow.dj-link or its global listeners."
  [config clock-ms]
  {:open!
   (fn [receive!]
     (let [token (Object.) components (atom nil) closed? (atom false)
           close! (fn []
                    (when (compare-and-set! closed? false true)
                      (when-let [{:keys [finder beats virtual peer-listener beat-listener status-listener]} @components]
                        (try (.removeDeviceAnnouncementListener finder peer-listener) (catch Exception _))
                        (try (.removeBeatListener beats beat-listener) (catch Exception _))
                        (when status-listener (try (.removeUpdateListener virtual status-listener) (catch Exception _)))
                        (when (:status? config) (try (.stop virtual) (catch Exception _)))
                        (try (.stop beats) (catch Exception _)) (try (.stop finder) (catch Exception _)))
                      (locking beatlink-lease (when (identical? token @beatlink-lease) (reset! beatlink-lease nil)))))]
       (try
       (locking beatlink-lease
         (when @beatlink-lease (fail! :beat-link-busy "Beat Link is already owned by another session"))
         (let [finder (singleton "org.deepsymmetry.beatlink.DeviceFinder")
               beats (singleton "org.deepsymmetry.beatlink.BeatFinder")
               virtual (singleton "org.deepsymmetry.beatlink.VirtualCdj")]
           (when (some #(.isRunning %) [finder beats virtual])
             (fail! :beat-link-busy "Beat Link components are already running outside this owner"))
           (reset! beatlink-lease token)
           (let [send! (fn [event] (when-not @closed? (receive! (assoc event :source-id (:source-id config)))))
                 peer-listener (listener "org.deepsymmetry.beatlink.DeviceAnnouncementListener"
                                         {"deviceFound" #(send! {:type :peer/found :peer (announcement-data % (clock-ms))})
                                          "deviceLost" #(send! {:type :peer/lost :peer (announcement-data % (clock-ms))})})
                 beat-listener (listener "org.deepsymmetry.beatlink.BeatListener"
                                         {"newBeat" #(send! (beat-data % (clock-ms) (System/nanoTime)))})
                 status-listener (when (:status? config)
                                   (listener "org.deepsymmetry.beatlink.DeviceUpdateListener"
                                             {"received" (fn [update]
                                                           (when (= "org.deepsymmetry.beatlink.CdjStatus" (.getName (class update)))
                                                             (let [observed (clock-ms) age (max 0.0 (/ (- (System/nanoTime) (.getTimestamp update)) 1000000.0))
                                                                   bpm (.getEffectiveTempo update)]
                                                               (send! {:type :beat-link/status :time-ms (max 0.0 (- observed age))
                                                                       :bpm (when (and (not= 65535 (.getBpm update)) (finite? bpm) (pos? bpm)) bpm)
                                                                       :playing? (.isPlaying update) :tempo-master? (.isTempoMaster update)
                                                                       :bar-meaningful? (.isBeatWithinBarMeaningful update)
                                                                       :reported-beat-number (.getBeatNumber update)
                                                                       :peer {:device-number (.getDeviceNumber update) :device-name (.getDeviceName update)
                                                                              :address (.getHostAddress (.getAddress update))}}))))}))]
             (reset! components {:finder finder :beats beats :virtual virtual :peer-listener peer-listener
                                 :beat-listener beat-listener :status-listener status-listener}))))
         (let [{:keys [finder beats virtual peer-listener beat-listener status-listener]} @components]
           (.addDeviceAnnouncementListener finder peer-listener) (.addBeatListener beats beat-listener)
           (when status-listener (.addUpdateListener virtual status-listener))
           (.start finder) (.start beats)
           (when (and (:status? config) (not (.start virtual))) (fail! :no-dj-peers "No Pro DJ Link peers became available"))
           (doseq [peer (.getCurrentDevices finder)]
             (receive! {:type :peer/found :source-id (:source-id config) :peer (announcement-data peer (clock-ms))}))
           {:close! close!})
         (catch Throwable error (close!) (throw error)))))
   :close! (fn [handle] ((:close! handle)))})

(defn- peer-key [peer] [(:device-number peer) (:address peer)])

(defn- paired-peer? [config peers peer]
  (pairing/matches-pairing? (get-in config [:beat-link :peer])
                           (assoc peer :hardware-address (get-in peers [(peer-key peer) :hardware-address]))))

(defn receive! [manager run event at]
  (let [{:keys [config peers]} @(:state manager)]
    (case (:type event)
      (:peer/found :peer/lost)
      (let [peer (:peer event) key (peer-key peer)]
        (if (= :peer/found (:type event))
          (swap! (:state manager) update :peers assoc key peer)
          (swap! (:state manager) update :peers dissoc key))
        (when (and (= :peer/lost (:type event)) (paired-peer? config peers peer))
          (apply-clock! manager run {:type :source/lost :source-id (get-in config [:beat-link :source-id]) :time-ms at}))
        (emit! manager run event))
      (:beat-link/beat :beat-link/status)
      (when (paired-peer? config peers (:peer event))
        (when (or (not= :beat-link/beat (:type event)) (:bpm event))
          (apply-clock! manager run (assoc event :align-bars? (get-in config [:beat-link :align-bars?]))))))))

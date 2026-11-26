(ns afterglow.control.devices.push-3.display
  "Tethered Push 3 image sink. Cached USB refresh is independent of browser capture."
  (:require [afterglow.control.devices.push-3.screen :as screen]
            [afterglow.control.devices.push-3.usb :as usb]
            [afterglow.control.devices.transports :as transports]))

(def ^:private sample-limit 4096)

(defn- sample [samples value]
  (let [samples (conj (or samples []) value)]
    (if (> (count samples) sample-limit) (subvec samples (- (count samples) sample-limit)) samples)))

(defn- record-frame [stats start-ns header-ns payload-ns bytes]
  (cond-> (-> stats
              (update :frames (fnil inc 0))
              (update :bytes (fnil + 0) bytes)
              (update :header-ns sample header-ns)
              (update :payload-ns sample payload-ns)
              (assoc :last-start-ns start-ns)
              (update :first-start-ns #(or % start-ns)))
    (:last-start-ns stats) (update :interval-ns sample (- start-ns (:last-start-ns stats)))))

(defn- stop! [{:keys [state backend wire]}]
  (let [{:keys [open? cancel]} @state]
    (when open?
      (swap! state #(-> % (assoc :open? false) (dissoc :receipt)))
      (try (when cancel (cancel))
           (finally ((:close! backend) wire))))))

(defn- present! [{:keys [state backend wire header pixels] :as handle}]
  (let [{:keys [open? ready? receipt]} @state]
    (when (and open? ready?)
      (try (let [start (System/nanoTime)
                 _ ((:write! backend) wire header)
                 written (System/nanoTime)
                 ^bytes payload (:wire pixels)
                 _ ((:write! backend) wire payload)
                 done (System/nanoTime)]
             (swap! state #(-> % (dissoc :receipt)
                               (update :stats record-frame start (- written start) (- done written)
                                       (+ (alength ^bytes header) (alength payload))))))
           receipt
           (catch Throwable error
             (swap! state #(-> % (dissoc :receipt) (assoc :failure error)))
             (stop! handle)
             (throw error))))))

(defn- render! [{:keys [lock state pixels] :as handle} image receipt]
  (when-let [completed (locking lock
                         (when-let [error (:failure @state)] (throw error))
                         (when-not (:open? @state) (throw (ex-info "Push 3 display is closed" {})))
                         (screen/encode! pixels image)
                         (swap! state assoc :receipt receipt)
                         (when-not (:ready? @state)
                           (swap! state assoc :ready? true)
                           (present! handle)))]
    (completed)))

(defn- summary-ms [samples]
  (when (seq samples)
    (let [sorted (vec (sort samples)) n (count sorted)
          at #(/ (nth sorted (min (dec n) (long (Math/floor (* % n))))) 1e6)]
      {:samples n :min-ms (/ (first sorted) 1e6) :median-ms (at 0.5) :p95-ms (at 0.95)
       :max-ms (/ (peek sorted) 1e6)})))

(defn refresh-receipt
  "Measured refresh of an open or closed sink handle: frames and bytes sent,
  achieved frames per second between the first and last frame start, frame
  intervals and late intervals (over 1.5 periods), per-transfer header and
  payload times, the sink open time and, for the libusb backend, its timing.
  Distributions cover at most the most recent 4096 frames."
  [{:keys [state wire target-hz open-ms]}]
  (let [{:keys [frames bytes first-start-ns last-start-ns interval-ns header-ns payload-ns]} (:stats @state)
        elapsed (when (and first-start-ns (not= first-start-ns last-start-ns))
                  (/ (- last-start-ns first-start-ns) 1e9))
        period-ns (when target-hz (/ 1e9 target-hz))]
    (cond-> {:frames (or frames 0) :bytes (or bytes 0) :target-hz target-hz :open-ms open-ms
             :frames-per-second (when elapsed (/ (dec frames) elapsed))
             :elapsed-ms (when elapsed (* 1000 elapsed))
             :interval (summary-ms interval-ns)
             :late-intervals (when period-ns (count (filter #(> % (* 1.5 period-ns)) interval-ns)))
             :header-transfer (summary-ms header-ns)
             :payload-transfer (summary-ms payload-ns)
             :failed? (boolean (:failure @state))}
      (and (map? wire) (:timing wire)) (assoc :usb (:timing wire)))))

(defn sink
  "Choose :bus and :address from usb/locations, or inject a replay backend.
  One transport owner resends the latest packed frame on a fixed grid of
  :refresh-hz deadlines (default 30), so transfer time does not lower the
  rate; a late frame skips the deadlines it missed. No new browser capture or
  show evaluation is needed for a static screen. A failed or partial transfer
  closes the native handle. Optional :render-with-receipt! takes a completion
  callback invoked only after both writes for that frame succeed. A newer
  frame replaces any packed frame waiting for transfer and its receipt.
  refresh-receipt reports the measured rate and transfer times."
  [{:keys [backend schedule! refresh-hz] :or {refresh-hz 30} :as options}]
  (let [backend (or backend {:open! usb/open! :write! usb/write! :close! usb/close!})
        ;; An injected schedule owns its own cadence unless a rate is also given.
        target-hz (when (or (nil? schedule!) (contains? options :refresh-hz)) refresh-hz)
        schedule! (or schedule! (transports/deadline-scheduler refresh-hz))]
    {:device :push-3 :input :image
     :open! (fn []
              (let [pixels (screen/buffers) header (screen/header) lock (Object.)
                    state (atom {:open? true})
                    start (System/nanoTime)
                    wire ((:open! backend) (dissoc options :backend :schedule! :refresh-hz))
                    handle {:pixels pixels :header header :lock lock :backend backend :state state :wire wire
                            :target-hz target-hz :open-ms (/ (- (System/nanoTime) start) 1e6)}]
                (try (let [cancel (schedule! #(when-let [completed (locking lock (present! handle))]
                                                (completed)))]
                       (swap! state assoc :cancel cancel)
                       handle)
                     (catch Throwable e (stop! handle) (throw e)))))
     :render! (fn [handle image] (render! handle image nil))
     :render-with-receipt! render!
     :close! (fn [{:keys [lock] :as handle}] (locking lock (stop! handle)))}))

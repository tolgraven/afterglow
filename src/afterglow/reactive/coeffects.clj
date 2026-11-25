(ns afterglow.reactive.coeffects
  "Demand-owned sources for the JVM reaction graph. The graph lock serializes
  registration, lifetime and scheduling. Workers only update their private slot."
  (:require [afterglow.time :as time])
  (:import [java.util.concurrent ArrayBlockingQueue Future RejectedExecutionException ThreadFactory
            ScheduledThreadPoolExecutor ThreadPoolExecutor ThreadPoolExecutor$AbortPolicy TimeUnit]))

(defn- threads [label]
  (reify ThreadFactory
    (newThread [_ task] (doto (Thread. task label) (.setDaemon true)))))

(defn create []
  {:definitions (volatile! {}) :active (volatile! {})
   :executor (delay (ThreadPoolExecutor. 2 2 30 TimeUnit/SECONDS (ArrayBlockingQueue. 32)
                                          (threads "afterglow-reactive-sampler") (ThreadPoolExecutor$AbortPolicy.)))
   :scheduler (delay (doto (ScheduledThreadPoolExecutor. 1 (threads "afterglow-reactive-schedule"))
                       (.setRemoveOnCancelPolicy true)))})

(defn fork [manager] (assoc manager :active (volatile! {})))

(defn- sampling-interval [interval]
  (let [[unit value] (when (and (map? interval) (= 1 (count interval))) (first interval))]
    (if (= :frames unit)
      (do
        (when-not (and (integer? value) (pos? value))
          (throw (ex-info "Sampling frame interval must be a positive integer" {:interval interval})))
        interval)
      (let [duration (if (= :fps unit)
                       (do
                         (when-not (and (time/finite-number? value) (pos? value))
                           (throw (ex-info "Sampling fps must be positive" {:interval interval})))
                         {:ms (/ 1000.0 value)})
                       interval)]
        (when-not (pos? (:value (time/normalize-duration duration)))
          (throw (ex-info "Sampling interval must be positive" {:interval interval})))
        duration))))

(defn- stop! [manager entry]
  (locking entry
    (vreset! (:stopped? entry) true)
    (when-let [ref (:ref entry)] (remove-watch ref (:watch-key entry)))
    (when-let [^Future task @(:schedule entry)] (.cancel task false))
    (when-let [^Future f @(:job entry)]
      (.cancel f true)
      (.remove ^ThreadPoolExecutor @(:executor manager) ^Runnable f))))

(defn retain! [manager ids]
  (doseq [[id entry] @(:active manager) :when (not (contains? ids id))]
    (vswap! (:active manager) dissoc id)
    (stop! manager entry)))

(defn adopt! [manager staged]
  (retain! manager #{})
  (vreset! (:active manager) @(:active staged)))

(defn close! [manager]
  (retain! manager #{})
  (when (realized? (:scheduler manager)) (.shutdownNow ^ScheduledThreadPoolExecutor @(:scheduler manager)))
  (when (realized? (:executor manager)) (.shutdownNow ^ThreadPoolExecutor @(:executor manager))))

(defn register!
  "Background intervals may count committed show frames with {:frames n}.
  Frame buckets and results belong to one show identity and epoch. Other
  intervals use a physical scheduler or published musical time."
  [manager id {:keys [mode ref sample interval] :or {mode :demand} :as definition}]
  (when-not (and (keyword? id)
                 (if ref
                   (and (instance? clojure.lang.IRef ref) (not sample) (not interval))
                   (and (fn? sample) (#{:demand :frame :background} mode)
                        (or (= :background mode) (nil? interval)))))
    (throw (ex-info "Expected a watched reference or a sampled coeffect" {:id id :mode mode})))
  (let [timing (when (= :background mode) (sampling-interval (or interval {:fps 10})))]
    (when-let [old (get @(:active manager) id)]
      (vswap! (:active manager) dissoc id)
      (stop! manager old))
    (vswap! (:definitions manager) assoc id
            (assoc definition :mode (if ref :ref mode) :interval timing)))
  id)

(defn active-ids [manager] (keys @(:active manager)))

(defn- activate! [manager id db]
  (let [active (get @(:active manager) id)
        owner (:frame-owner active)]
    (if (and active (or (nil? owner) (= owner [(:show-id db) (:epoch db)])))
      active
      (if-let [{:keys [ref initial interval] :as definition} (get @(:definitions manager) id)]
        (let [entry (assoc definition :frame-owner (when (:frames interval) [(:show-id db) (:epoch db)])
                           :slot (atom {:value initial}) :job (volatile! nil)
                           :timer (volatile! nil) :schedule (volatile! nil) :db (atom nil) :stopped? (volatile! false)
                           :changed (atom 0) :watch-key (Object.))]
          ;; A canceled sampler can still finish. Its retired slot stays private.
          (when active (stop! manager active))
          ;; A watch only invalidates. Reading @ref at capture avoids older
          ;; out-of-order callbacks overwriting later concurrent resets.
          (when ref (add-watch ref (:watch-key entry) (fn [_ _ old new]
                                                        (when (not= old new) (swap! (:changed entry) inc)))))
          (vswap! (:active manager) assoc id entry)
          entry)
        (throw (ex-info "Unknown reactive coeffect" {:id id}))))))

(defn- submit! [manager {:keys [job sample slot stopped?] :as entry} db]
  (locking entry
    (let [^Future prev @job]
      (when (and (not @stopped?) (or (nil? prev) (.isDone prev)))
        (let [run (fn []
                    (try (reset! slot {:value (sample db)})
                         (catch InterruptedException _ (.interrupt (Thread/currentThread)))
                         (catch Exception e (reset! slot {:error e}))
                         (catch AssertionError e (reset! slot {:error e}))))]
          (try
            (vreset! job (.submit ^ThreadPoolExecutor @(:executor manager) ^Runnable run))
            true
            ;; A busy pool retries next deadline. Slow work never spills onto the owner.
            (catch RejectedExecutionException _ false)))))))

(defn- schedule-bucket! [manager {:keys [timer] :as entry} db bucket]
  (when (and (not= bucket @timer) (submit! manager entry db))
    (vreset! timer bucket)))

(defn- schedule! [manager {:keys [interval schedule] :as entry} db]
  (if-let [frames (:frames interval)]
    (let [frame-number (:frame-number db)]
      (when (and (integer? frame-number) (not (neg? frame-number)))
        (schedule-bucket! manager entry db (quot frame-number frames))))
    (let [clock (time/frame-clock db) {:keys [value unit]} (time/normalize-duration interval (:meter clock))]
      (if (= :ms unit)
        (do
          (reset! (:db entry) db)
          (when-not @schedule
            (let [period (max 1 (long (Math/ceil (* 1e6 (min (double value) 9.0e12)))))]
              (vreset! schedule (.scheduleWithFixedDelay ^ScheduledThreadPoolExecutor @(:scheduler manager)
                                  ^Runnable (fn [] (submit! manager entry @(:db entry)))
                                  0 period TimeUnit/NANOSECONDS)))))
        (when (and (time/finite-number? (:beat clock)) (not= false (:playing? clock)))
          (schedule-bucket! manager entry db (Math/floor (/ (double (:beat clock)) value))))))))

(defn capture
  "Sample once for the frozen transaction. An asynchronous result belongs only
  to the entry that requested it; removing or replacing a source orphans it."
  [manager id db restoring?]
  (let [{:keys [mode ref sample select changed slot] :as entry} (activate! manager id db)]
    (try
      (case mode
        :ref (let [version @changed cached @slot]
               (if (= version (:version cached)) cached
                   (reset! slot {:value (if select (select @ref) @ref) :version version})))
        :demand {:value (sample db)}
        :frame {:value (sample db)}
        :background (do (when-not restoring? (schedule! manager entry db)) @slot))
      (catch Exception e {:error e})
      (catch AssertionError e {:error e}))))

(defn demand-only? [manager id]
  (= :demand (get-in @(:definitions manager) [id :mode])))

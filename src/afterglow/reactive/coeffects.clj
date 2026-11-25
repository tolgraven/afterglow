(ns afterglow.reactive.coeffects
  "Demand-owned sources for the JVM reaction graph. The graph lock serializes
  registration, lifetime and scheduling. Workers only update their private slot."
  (:require [afterglow.runtime.faults :as faults]
            [afterglow.time :as time])
  (:import [java.util.concurrent ArrayBlockingQueue Future RejectedExecutionException ThreadFactory
            ScheduledThreadPoolExecutor ThreadPoolExecutor ThreadPoolExecutor$AbortPolicy TimeUnit]))

(defn- threads [label]
  (reify ThreadFactory
    (newThread [_ task] (doto (Thread. task label) (.setDaemon true)))))

(defn create []
  {:definitions (volatile! {}) :active (volatile! {}) :oscillators (volatile! {})
   :oscillator-anchors (volatile! {})
   :executor (delay (ThreadPoolExecutor. 2 2 30 TimeUnit/SECONDS (ArrayBlockingQueue. 32)
                                          (threads "afterglow-reactive-sampler") (ThreadPoolExecutor$AbortPolicy.)))
   :scheduler (delay (doto (ScheduledThreadPoolExecutor. 1 (threads "afterglow-reactive-schedule"))
                       (.setRemoveOnCancelPolicy true)))})

(defn fork [manager] (assoc manager :active (volatile! {})))

;; Named oscillators are portable data. Their committed position is derived
;; from frozen db transports. One anchor per oscillator, advanced only by owner
;; publications, keeps bar and phrase periods continuous across meter changes,
;; so replaying the same publications reproduces the same buckets.
(defn- validate-oscillator [id {:keys [period phase] :or {phase 0} :as definition}]
  (when-not (and (keyword? id) (map? definition) (= #{} (disj (set (keys definition)) :period :phase))
                 (map? period) (= 1 (count period)) (#{:beats :bars :phrases} (ffirst period))
                 (time/finite-number? (val (first period))) (pos? (val (first period)))
                 (time/finite-number? phase))
    (throw (ex-info "A reactive oscillator needs a keyword name, a positive :beats, :bars or :phrases :period and a finite :phase"
                    {:type :afterglow.reactive/invalid-oscillator :oscillator id :definition definition})))
  {:period period :phase phase})

(defn register-oscillator!
  "Register or replace a definition. A new or changed definition restarts its
  anchor and clears the bucket of every active source following it, so the
  next publication samples even when the bucket number is unchanged."
  [manager id definition]
  (let [definition (validate-oscillator id definition)]
    (when-not (= definition (get @(:oscillators manager) id))
      (vswap! (:oscillators manager) assoc id definition)
      (vswap! (:oscillator-anchors manager) dissoc id)
      (doseq [[_ entry] @(:active manager) :when (= id (:oscillator entry))]
        (vreset! (:timer entry) nil)))
    id))

(defn remove-oscillator! [manager id]
  (let [present? (contains? @(:oscillators manager) id)]
    (vswap! (:oscillators manager) dissoc id)
    (vswap! (:oscillator-anchors manager) dissoc id)
    present?))

(defn oscillators [manager] @(:oscillators manager))

(defn- unknown-oscillator [manager id]
  (let [registered (vec (sort (keys @(:oscillators manager))))]
    (ex-info (str "Unknown reactive oscillator " id "; registered oscillators: " registered)
             {:type :afterglow.reactive/unknown-oscillator :oscillator id :registered registered})))

(defn- oscillator-clock [id db]
  (let [{:keys [beat meter]} (time/frame-clock db)]
    (when (some? beat)
      (when-not (time/finite-number? beat)
        (throw (ex-info "Oscillator transport beat must be finite or nil" {:oscillator id})))
      ;; A decimal beat divided by a ratio period may not terminate.
      {:beat (if (decimal? beat) (rationalize beat) beat)
       :meter (time/normalize-meter meter)
       :owner [(:show-id db) (:epoch db)]})))

(defn- anchored-position [{:keys [period]} {:keys [beat position meter]} at-beat]
  (+ position (/ (- at-beat beat) (time/duration->beats period meter))))

(defn- advance-anchor
  "A new show identity or epoch starts at phase + beat / period. A meter change
  re-anchors at the current beat, continuing from the position the previous
  meter reached there. Absent a meter map, the change is placed at the first
  publication that carries it."
  [{:keys [phase] :as definition} anchor {:keys [beat meter owner]}]
  (cond
    (or (nil? anchor) (not= owner (:owner anchor)))
    {:owner owner :meter meter :beat 0 :position phase}

    (not= meter (:meter anchor))
    {:owner owner :meter meter :beat beat :position (anchored-position definition anchor beat)}

    :else anchor))

(defn observe-oscillators!
  "Advance every oscillator's anchor from one committed db on the owner. A
  malformed transport leaves the anchor; captures report that error."
  [manager db]
  (doseq [[id definition] @(:oscillators manager)]
    (try
      (when-let [clock (oscillator-clock id db)]
        (vswap! (:oscillator-anchors manager) update id #(advance-anchor definition % clock)))
      (catch Exception _ nil))))

(defn oscillator-position
  "Unwrapped cycle position of a named oscillator at the committed transport
  beat. Within one meter it is anchor position + elapsed beats / period-in-beats;
  from a fresh anchor that is phase + beat / period-in-beats. Exact when the beat
  and definition are rational. Nil while the beat is unavailable. Pure: it never
  advances the stored anchor."
  [manager id db]
  (let [definition (get @(:oscillators manager) id)]
    (when-not definition (throw (unknown-oscillator manager id)))
    (when-let [{:keys [beat] :as clock} (oscillator-clock id db)]
      (anchored-position definition
                         (advance-anchor definition (get @(:oscillator-anchors manager) id) clock)
                         beat))))

(defn- sampling-interval [interval cycle-position]
  (let [[unit value] (when (and (map? interval) (= 1 (count interval))) (first interval))]
    (case unit
      :frames
      (do
        (when-not (and (integer? value) (pos? value))
          (throw (ex-info "Sampling frame interval must be a positive integer" {:interval interval})))
        interval)

      :cycles
      (do
        (when-not (and (time/finite-number? value) (pos? (double value)) (fn? cycle-position))
          (throw (ex-info "Sampling cycles require a positive interval and a cycle-position function"
                          {:interval interval})))
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
  [manager id {:keys [mode ref sample interval oscillator] :or {mode :demand} :as definition}]
  (when (and (contains? definition :oscillator)
             (not (and (= :background mode) (not ref) (not (contains? definition :cycle-position))
                       (map? interval) (contains? interval :cycles))))
    (throw (ex-info "A named :oscillator needs :mode :background and :interval {:cycles n}, without :cycle-position"
                    {:id id :mode mode :interval interval})))
  (when-not (and (keyword? id)
                 (or (not (or (contains? definition :cycle-position) (contains? definition :oscillator)))
                     (and (= :background mode) (not ref) (map? interval) (contains? interval :cycles)))
                 (if ref
                   (and (instance? clojure.lang.IRef ref) (not sample) (not interval))
                   (and (fn? sample) (#{:demand :frame :background} mode)
                        (or (= :background mode) (nil? interval)))))
    (throw (ex-info "Expected a watched reference or a sampled coeffect" {:id id :mode mode})))
  (when (contains? definition :oscillator)
    (when-not (keyword? oscillator)
      (throw (ex-info "A cycle :oscillator must be a registered oscillator name"
                      {:type :afterglow.reactive/unknown-oscillator :id id :oscillator oscillator})))
    (when-not (contains? @(:oscillators manager) oscillator)
      (throw (unknown-oscillator manager oscillator))))
  (let [definition (cond-> definition
                     (contains? definition :oscillator)
                     (assoc :cycle-position (fn [db] (oscillator-position manager oscillator db))))
        timing (when (= :background mode) (sampling-interval (or interval {:fps 10}) (:cycle-position definition)))]
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
        (let [frame-owner (when (or (:frames interval) (:cycles interval)) [(:show-id db) (:epoch db)])
              entry (assoc definition :frame-owner frame-owner
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

(defn- decimal-magnitude-below-interval? [^BigDecimal position interval]
  (let [magnitude (.abs position)]
    (neg? (if (ratio? interval)
            (.compareTo (.multiply magnitude (bigdec (denominator interval)))
                        (bigdec (numerator interval)))
            (.compareTo magnitude (bigdec interval))))))

(defn- cycle-bucket [position cycles]
  (let [bucket (if (and (rational? position) (rational? cycles))
                 (if (and (decimal? position) (zero? (double position))
                          (decimal-magnitude-below-interval? position cycles))
                   ;; Keep very small decimal positions at their original scale.
                   (if (neg? position) -1 0)
                   (let [quotient (/ (rationalize position) (rationalize cycles))
                         whole (quot quotient 1)]
                     (if (< quotient whole) (dec' whole) whole)))
                 (Math/floor (/ (double position) (double cycles))))]
    (when-not (time/finite-number? bucket)
      (throw (ex-info "Sampling cycle bucket exceeds the finite range" {})))
    ;; Represent both paths as integers so one bucket survives a numeric type change.
    (if (float? bucket) (.toBigInteger (BigDecimal. (double bucket))) bucket)))

(defn- schedule-cycle! [manager {:keys [cycle-position] :as entry} db cycles]
  (when (not= false (:playing? (time/frame-clock db)))
    (when-some [position (cycle-position db)]
      (when-not (time/finite-number? position)
        (throw (ex-info "Sampling cycle position must be finite or nil" {})))
      (schedule-bucket! manager entry db (cycle-bucket position cycles)))))

(defn- schedule! [manager {:keys [interval schedule] :as entry} db]
  (let [[unit amount] (first interval)]
    (case unit
      :frames
      (let [frame-number (:frame-number db)]
        (when (and (integer? frame-number) (not (neg? frame-number)))
          (schedule-bucket! manager entry db (quot frame-number amount))))

      :cycles (schedule-cycle! manager entry db amount)

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
            (schedule-bucket! manager entry db (Math/floor (/ (double (:beat clock)) value)))))))))

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
      (catch Throwable e
        (if (faults/recoverable? e) {:error e} (throw e))))))

(defn demand-only? [manager id]
  (= :demand (get-in @(:definitions manager) [id :mode])))

(ns afterglow.render.gpu.movement
  "Show-owned boundary for calibrated moving-head output. The native solver is
  loaded on demand. Each call packs only its own post-blend movement results."
  (:require [afterglow.render.frame :as frame]
            [afterglow.runtime.faults :as faults])
  (:import [java.io Closeable]
           [java.util.concurrent ArrayBlockingQueue Callable ExecutionException Future RejectedExecutionException
            Semaphore ThreadFactory ThreadPoolExecutor TimeUnit TimeoutException]))

(defrecord Movement [^ThreadPoolExecutor worker permit resident options done]
  Closeable
  (close [_]
    (.shutdown worker)
    (when-let [error @done] (throw error))))

(defn open!
  "Create an owner for one show. :budget-ms is the per-frame GPU wait budget
  (default 25). :timeout-ms bounds the native fence (default 1000).
  Native allocation happens on the first frame with eligible movement."
  ([] (open! {}))
  ([{:keys [budget-ms timeout-ms] :or {budget-ms 25 timeout-ms 1000}}]
   (when-not (and (integer? budget-ms) (<= 1 budget-ms 10000)
                  (integer? timeout-ms) (<= 1 timeout-ms 10000))
     (throw (ex-info "Movement budget and fence timeout must be 1..10000 ms" {})))
   (let [resident (volatile! nil)
         done (promise)
         factory (reify ThreadFactory
                   (newThread [_ task] (doto (Thread. task "afterglow-movement") (.setDaemon true))))
         worker (proxy [ThreadPoolExecutor]
                    [1 1 0 TimeUnit/MILLISECONDS (ArrayBlockingQueue. 1) factory]
                  (terminated []
                    (deliver done (try (when-let [solver (:solver @resident)] (.close ^Closeable solver))
                                       nil (catch Throwable error error)))
                    (vreset! resident nil)))]
     (->Movement worker (Semaphore. 1) resident {:budget-ms budget-ms :timeout-ms timeout-ms} done))))

(defn close!
  "Stop admissions and retire the last context after any pending native call.
  With a timeout, return false while cleanup continues on the worker."
  ([^Movement owner] (.close owner) true)
  ([owner timeout-ms]
   (when-not (and (integer? timeout-ms) (<= 0 timeout-ms Long/MAX_VALUE))
     (throw (ex-info "Shutdown timeout must be a nonnegative integer" {})))
   (.shutdown ^ThreadPoolExecutor (:worker owner))
   (let [answer (deref (:done owner) timeout-ms ::pending)]
     (cond (= ::pending answer) false (some? answer) (throw answer) :else true))))

(defn- fail-or-fallback [error reason]
  (if (faults/recoverable? error)
    {:reason reason :error (.getName (class error))}
    (throw error)))

(defn- native-rig! [{:keys [resident options]} patch]
  ;; Only the worker accesses the cached solver. An unavailable context stays
  ;; retired until a new patch is installed or the caller reopens the owner.
  (if (identical? patch (:patch @resident))
    @resident
    (do
      (when-let [old (:solver @resident)] (.close ^Closeable old))
      (vreset! resident
               (assoc (try
                        (let [open (requiring-resolve 'afterglow.render.native-gpu/open!)
                              solve (requiring-resolve 'afterglow.render.native-gpu/solve-selected!)]
                          {:solver (open patch (select-keys options [:timeout-ms])) :solve solve})
                        (catch Throwable error (fail-or-fallback error :unavailable)))
                      :patch patch)))))

(defn- draw! [owner patch targets options]
  (let [{:keys [solver solve reason error]} (native-rig! owner patch)]
    (if reason
      {:reason reason :error error}
      (try (let [solved (solve solver targets options)]
             (cond-> {:solved solved} (empty? solved) (assoc :reason :ambiguous)))
           (catch Throwable cause
             (let [status (fail-or-fallback cause :native-error)]
               (when @(:closed? solver)
                 (vreset! (:resident owner) (assoc status :patch patch)))
               status))))))

(defn- draw-before! [{:keys [worker permit] :as owner} patch targets options deadline]
  (let [^ThreadPoolExecutor worker worker
        ^Semaphore permit permit]
    (cond
      (.isShutdown worker) {:reason :closed}
      (<= deadline (System/nanoTime)) {:reason :timeout}
      (not (.tryAcquire permit)) {:reason :busy}
      :else
      (try
        (let [job ^Future (.submit worker ^Callable (fn []
                                                      (try (draw! owner patch targets options)
                                                           (finally (.release permit)))))
              result (.get job (long (max 0 (-' deadline (System/nanoTime)))) TimeUnit/NANOSECONDS)]
          (if (> deadline (System/nanoTime)) result {:reason :timeout}))
        ;; A late draw owns only its caller's captured arguments. Never cancel
        ;; or interrupt driver work, and never queue a later frame behind it.
        (catch TimeoutException _ {:reason :timeout})
        (catch RejectedExecutionException _ (.release permit) {:reason :closed})
        (catch ExecutionException error (throw (.getCause error)))))))

(defn- shader-number? [value]
  ;; Stay in the reference arithmetic for ratios, decimals and large integers.
  ;; Limit the exponent so squared vector lengths and coordinate differences fit.
  (and (or (float? value) (and (integer? value) (<= -16777216 value 16777216)))
       (let [n (abs (double value))] (or (zero? n) (<= 1.0e-16 n 1.0e16)))))

(defn- shader-axis? [cal]
  (every? shader-number? (if (map? cal) [(:min-deg cal) (:max-deg cal)] cal)))

(defn- stable-difference? [target origin]
  ;; Subtraction on a large world origin can lose a whole relative axis in f32.
  (let [delta (- (double target) (double origin))
        gpu-delta (double (unchecked-float (- (double (unchecked-float target)) (double (unchecked-float origin)))))]
    (<= (abs (- delta gpu-delta)) (* 1.0e-6 (abs delta)))))

(defn- eligible? [patch id {:keys [aim direction]} pan]
  (let [{:keys [position rotation-deg calibration]} (get (:by-id patch) id)]
    (and (every? shader-number? (or aim direction))
         (every? shader-number? position) (every? shader-number? rotation-deg)
         (shader-axis? (:pan calibration)) (shader-axis? (:tilt calibration))
         (or (nil? pan) (shader-number? pan))
         (or (nil? aim) (every? true? (map stable-difference? aim position))))))

(defn resolve-contributions!
  "Resolve ordered contribution blocks for a compiled patch. The reference
  renderer blends first. Active, shader-representable world-space aims and
  directions can then use calibrated native rotation ahead of physical packing.
  All frame options are supported. Optional :deadline-nanos is an absolute
  System/nanoTime deadline for the GPU stage. :movement describes this frame."
  ([owner patch contributions] (resolve-contributions! owner patch contributions {}))
  ([owner patch contributions options]
   (when-not (= :afterglow.render.frame/patch (:type patch))
     (throw (ex-info "Supply a compiled Afterglow patch" {})))
   (let [budget-end (+ (System/nanoTime) (* 1000000 (:budget-ms (:options owner))))
         requested (get options :deadline-nanos budget-end)]
     (when-not (and (integer? requested) (<= Long/MIN_VALUE requested Long/MAX_VALUE))
       (throw (ex-info "Movement deadline must use System/nanoTime" {})))
     (let [deadline (min budget-end requested)
           {:keys [targets pack reference-ids]} (frame/prepare-movement-frame patch contributions options)
           ;; Compact arrays belong to the published frame. Detach only the
           ;; accepted scalar pans before a native job can outlive this call.
           ids (vec (keys targets))
           pans (when (seq ids) (zipmap ids (frame/previous-pans patch ids options)))
           active (into {} (filter (fn [[id target]] (and (not (contains? reference-ids id)) (eligible? patch id target (get pans id))))) targets)
           history {:previous-values (into {} (map (fn [id] [id {:pan (get pans id)}])) (keys active))}
           result (cond (empty? targets) {:reason :no-geometry}
                        (empty? active) {:reason :cpu-input}
                        :else (draw-before! owner patch active history deadline))
           solved (:solved result {})
           details (merge (dissoc result :solved)
                          {:backend (if (seq solved) :native-gpu :cpu)
                           :gpu-heads (count solved) :cpu-heads (- (count targets) (count solved))})]
       (assoc (pack solved) :movement details)))))

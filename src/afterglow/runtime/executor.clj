(ns afterglow.runtime.executor
  "Explicit bounded worker boundary for the pure runtime.

  Requiring this namespace starts no threads. Create a pool at show startup, pass
  its mapper to engine/advance, and close it at shutdown. Work is bounded and a
  whole mapping call has one deadline; a failed frame is never returned partly."
  (:import [java.io Closeable]
           [java.util ArrayList]
           [java.util.concurrent ArrayBlockingQueue Callable ExecutionException
            Future FutureTask ThreadFactory ThreadPoolExecutor
            ThreadPoolExecutor$AbortPolicy TimeUnit]
           [java.util.concurrent.atomic AtomicLong]
           [java.util.concurrent.locks ReentrantLock]))

(defrecord WorkerPool [^ThreadPoolExecutor executor ^ReentrantLock gate
                       timeout-ms max-in-flight]
  Closeable
  (close [_]
    (.shutdownNow executor)
    (try
      (.awaitTermination executor 1 TimeUnit/SECONDS)
      (catch InterruptedException _
        (.interrupt (Thread/currentThread))))))

(defn create
  "Create an explicitly owned bounded executor, without starting worker threads.

  :workers defaults to 2, :queue-size to 32, :timeout-ms to 100. These are positive
  integers. :queue-size is the extra in-flight allowance beyond worker count;
  at most workers + queue-size jobs are submitted simultaneously. The backing
  queue can hold that whole window while worker threads are waking up. One
  mapping call may own a pool at a time; concurrent calls fail immediately.
  Workers are daemon threads as a final process-exit fallback, not a substitute
  for closing the pool. A task that ignores interruption can outlive a timeout;
  the shell should retire such a pool and report the failed frame."
  ([] (create {}))
  ([{:keys [workers queue-size timeout-ms]
     :or {workers 2 queue-size 32 timeout-ms 100}}]
   (doseq [[key value limit] [[:workers workers 1024]
                              [:queue-size queue-size 1000000]
                              [:timeout-ms timeout-ms 3600000]]]
     (when-not (and (integer? value) (pos? value) (<= value limit))
       (throw (ex-info "Invalid bounded executor option"
                       {:type ::invalid-option :option key :value value}))))
   (let [sequence-number (AtomicLong. 0)
         factory (reify ThreadFactory
                   (newThread [_ task]
                     (doto (Thread. task (str "afterglow-runtime-" (.incrementAndGet sequence-number)))
                       (.setDaemon true))))
         executor (ThreadPoolExecutor. workers workers 0 TimeUnit/MILLISECONDS
                                       (ArrayBlockingQueue. (+ workers queue-size))
                                       factory (ThreadPoolExecutor$AbortPolicy.))]
     (->WorkerPool executor (ReentrantLock.) timeout-ms (+ workers queue-size)))))

(defn close!
  "Interrupt queued/running work and wait at most one second for termination."
  [^WorkerPool pool]
  (.close pool))

(defn map-work
  "Map f across jobs using pool, returning results in completion order.

  Throws typed ex-info on timeout, worker failure, closed/busy pool or rejection.
  All submitted futures are cancelled on exit; successful results are already
  complete, so cancellation has no effect on them. The deadline includes queue
  time and all jobs in this mapping call. The runtime restores semantic ordering."
  [^WorkerPool pool f jobs]
  (let [^ThreadPoolExecutor executor (:executor pool)
        ^ReentrantLock gate (:gate pool)]
    (when-not (.tryLock gate)
      (throw (ex-info "Worker pool already has a frame in flight" {:type ::busy})))
    (try
      (when (.isShutdown executor)
        (throw (ex-info "Worker pool is closed" {:type ::closed})))
      (let [completion (ArrayBlockingQueue. (:max-in-flight pool))
            submitted (ArrayList.)
            deadline (+ (System/nanoTime) (* 1000000 (long (:timeout-ms pool))))
            submit! (fn [job]
                      (let [task (proxy [FutureTask] [(reify Callable (call [_] (f job)))]
                                   (done [] (.add completion this)))]
                        (.add submitted task)
                        (.execute executor task)))]
        (try
          (loop [remaining (seq jobs) in-flight 0 results []]
            (cond
              (and remaining (< in-flight (:max-in-flight pool)))
              (do (submit! (first remaining))
                  (recur (next remaining) (inc in-flight) results))

              (zero? in-flight) results

              :else
              (let [remaining-ns (- deadline (System/nanoTime))
                    task (when (pos? remaining-ns)
                           (.poll completion remaining-ns TimeUnit/NANOSECONDS))]
                (when-not task
                  (throw (ex-info "Frame worker deadline exceeded"
                                  {:type ::timeout :timeout-ms (:timeout-ms pool)})))
                (recur remaining (dec in-flight) (conj results (.get ^Future task))))))
          (catch InterruptedException cause
            (.interrupt (Thread/currentThread))
            (throw (ex-info "Frame worker wait was interrupted" {:type ::interrupted} cause)))
          (catch ExecutionException cause
            (throw (ex-info "Frame worker failed" {:type ::worker-failed} (.getCause cause))))
          (catch java.util.concurrent.RejectedExecutionException cause
            (throw (ex-info "Frame work was rejected by the bounded pool"
                            {:type ::rejected} cause)))
          (finally
            (doseq [^Future task submitted]
              (.cancel task true))
            (.purge executor))))
      (finally
        (.unlock gate)))))

(defn mapper
  "Return the blocking [f jobs] mapper accepted by engine/advance."
  [pool]
  (partial map-work pool))

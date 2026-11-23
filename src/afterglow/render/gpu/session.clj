(ns afterglow.render.gpu.session
  "One show-owned native context, a bounded queue and a bounded LRU of shaders.
  Results belong to the submitting frame. This owner never publishes a frame."
  (:require [afterglow.render.gpu.expressions :as expressions]
            [afterglow.render.gpu.native-context :as context]
            [afterglow.render.gpu.lifecycle :as lifecycle]
            [afterglow.runtime.reuse :as reuse])
  (:import [java.io Closeable]
           [java.util LinkedHashMap]
           [java.util.concurrent ArrayBlockingQueue Callable ExecutionException Future FutureTask
            RejectedExecutionException ThreadFactory ThreadPoolExecutor ThreadPoolExecutor$AbortPolicy TimeUnit]))

(defn group
  "Capture immutable expression definitions and ordered xyz positions. Equal
  descriptions share a program; changing the definitions or physical order
  produces a new cache key. The descriptor can be shared by frame workers."
  ([outputs positions] (expressions/group outputs positions))
  ([outputs positions surface-uvs] (expressions/group outputs positions surface-uvs)))

(defn- shutdown! [^ThreadPoolExecutor executor gate]
  (locking gate
    (when-not (.isShutdown executor)
      ;; Clear waiting work without interrupting a native call already in progress.
      (let [waiting (java.util.ArrayList.)]
        (.drainTo (.getQueue executor) waiting)
        (doseq [^Future f waiting] (.cancel f false)))
      (.shutdown executor))))

(defrecord Session [owner ^ThreadPoolExecutor executor ^LinkedHashMap programs max-programs stats gate done]
  Closeable
  (close [_]
    (shutdown! executor gate)
    (when-let [failure @done] (throw failure))))

(defn open!
  "Acquire one OpenGL context. The queue bounds waiting jobs in addition to one
  active job. Defaults are eight resident programs, four waiting jobs and a
  1000 ms fence timeout on each submitted draw."
  ([] (open! {}))
  ([{:keys [max-programs queue-capacity timeout-ms]
     :or {max-programs 8 queue-capacity 4 timeout-ms 1000}}]
   (when-not (and (pos-int? max-programs) (pos-int? queue-capacity) (<= queue-capacity Integer/MAX_VALUE))
     (throw (ex-info "Program and queue capacities must be positive integers" {})))
   (let [queue (ArrayBlockingQueue. queue-capacity)
         gate (Object.) done (promise) cache (LinkedHashMap. 16 0.75 true)
         stats (atom {:hits 0 :misses 0 :evictions 0 :resident 0 :draws 0})
         factory (reify ThreadFactory
                   (newThread [_ run] (doto (Thread. run "afterglow-gpu") (.setDaemon true))))
         owner (context/open! ::session timeout-ms (constantly {}))]
     (try
       (let [executor (proxy [ThreadPoolExecutor]
                          [1 1 0 TimeUnit/MILLISECONDS queue factory (ThreadPoolExecutor$AbortPolicy.)]
                        (terminated []
                          (lifecycle/finish! done #(try (.close ^Closeable owner)
                                                        (finally (.clear cache)
                                                                 (swap! stats assoc :resident 0))))))]
         (.prestartCoreThread executor)
         (->Session owner executor cache max-programs stats gate done))
       (catch Throwable error (.close ^Closeable owner) (throw error))))))

(defn close!
  "Stop admission and cancel waiting futures. The active native call finishes
  before context destruction. With a timeout, false means cleanup continues
  on the owner; timeout never interrupts the driver."
  ([^Session session] (.close session) true)
  ([session timeout-ms]
   (when-not (and (integer? timeout-ms) (not (neg? timeout-ms)))
     (throw (ex-info "Shutdown timeout must be a nonnegative integer" {})))
   (shutdown! (:executor session) (:gate session))
   (let [result (deref (:done session) timeout-ms ::pending)]
     (cond (= ::pending result) false (some? result) (throw result) :else true))))

(defn status [{:keys [stats owner] :as session}]
  (let [^ThreadPoolExecutor executor (:executor session)]
    (merge @stats (select-keys (:resources owner) [:renderer :version])
           {:queued (.size (.getQueue executor)) :closed? (.isShutdown executor)
            :terminated? (realized? (:done session))})))

(defn- enqueue! [{:keys [owner executor gate] :as session} task]
  (let [^ThreadPoolExecutor pool executor
        call ^Callable (fn []
                         (try (task)
                              (finally (when @(:closed? owner) (shutdown! pool gate)))))
        job (proxy [FutureTask] [call]
              (cancel [_] (proxy-super cancel false))
              (done [] (when (.isCancelled ^Future this) (.remove pool this))))]
    (locking gate
      (when (.isShutdown pool) (throw (ex-info "GPU session is closed" {:type ::closed})))
      (try (.execute pool job)
           (catch RejectedExecutionException _
             (throw (ex-info "GPU session queue is full" {:type ::busy :queued (:queued (status session))})))))
    job))

(defn- release! [{:keys [owner programs stats]} key]
  (let [cache ^LinkedHashMap programs]
    (when-let [program (.remove cache key)]
      (context/invoke! owner #(expressions/release-program! % program))
      (swap! stats #(-> % (update :evictions inc) (assoc :resident (.size cache))))
      true)))

(defn- resident! [{:keys [owner programs max-programs stats] :as session} group]
  (let [cache ^LinkedHashMap programs]
    (if-let [ready (.get cache group)]
      (do (swap! stats update :hits inc) ready)
      (do
        (swap! stats update :misses inc)
        ;; Compile the replacement before freeing the least-recently-used program.
        (let [program (context/prepare! owner #(expressions/compile-program! % group))
              evaluate (reuse/evaluator
                        {:pure? true :inputs [[:uniforms]]}
                        (fn [{:keys [uniforms]}]
                          (let [batch (expressions/run-program! owner program uniforms)]
                            (when (pos? (:count program)) (swap! stats update :draws inc))
                            batch)))
              new-program (assoc program :evaluate evaluate)]
          (when (= max-programs (.size cache))
            (release! session (.next (.iterator (.keySet cache)))))
          (.put cache group new-program)
          (swap! stats assoc :resident (.size cache))
          new-program)))))

(defn submit!
  "Submit an immutable group and a captured environment, returning a Future
  for the owned CPU-compatible batch. A saturated queue immediately throws
  ::busy. No clocks, fixture positions or parameters are sampled later."
  [session group env]
  (when-not (instance? afterglow.render.gpu.expressions.Group group)
    (throw (ex-info "Use session/group to describe the expressions and ordered positions" {})))
  (let [inputs (expressions/capture-inputs (:bindings group) env)]
    (enqueue! session #((:evaluate (resident! session group)) {:uniforms inputs}))))

(defn- await-result [^Future future]
  (try (.get future) (catch ExecutionException error (throw (.getCause error)))))

(defn evaluate!
  "Submit a frame and wait for its independent CPU-compatible output arrays."
  [session group env]
  (await-result (submit! session group env)))

(defn evict!
  "Release this group's programs and buffers after preceding work completes.
  Return true if resident, false otherwise."
  [session group]
  (await-result (enqueue! session #(boolean (release! session group)))))

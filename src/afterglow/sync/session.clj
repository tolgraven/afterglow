(ns afterglow.sync.session
  "Queue, generation, clock and callback ownership shared by synchronization adapters."
  (:require [afterglow.control.clock :as clock])
  (:import [java.util.concurrent ArrayBlockingQueue RejectedExecutionException ThreadPoolExecutor]))

(defn fail! [code message] (throw (ex-info message {:sync/error code})))

(defn error-data [error]
  {:code (or (:sync/error (ex-data error)) :transport-error) :message (or (.getMessage ^Throwable error) (str (class error)))})

(defn now-ms [] (/ (double (System/nanoTime)) 1000000.0))

(def ^:dynamic *input-generation* nil)

(defn run-callbacks [run]
  (let [callbacks (:callbacks run)]
    (if (instance? clojure.lang.IDeref callbacks) @callbacks callbacks)))

(defn emit! [manager run event]
  (when-let [handler (:events! (run-callbacks run))]
    (try (when (= false (handler event)) (swap! (:state manager) update-in [:metrics :dropped-host-events] (fnil inc 0)))
         (catch Exception error
           (swap! (:state manager) #(-> % (update-in [:metrics :callback-errors] (fnil inc 0))
                                         (assoc :last-error (error-data error))))))))

(defn queue! [manager run event]
  (locking (:binding-lock run)
    (let [generation (or *input-generation* @(:binding-generation run))]
      (if (or @(:cancelled? run) (not (identical? run (:active @(:state manager))))
              (not= generation @(:binding-generation run))) false
        (if (.offer ^ArrayBlockingQueue (:queue run) (assoc event ::generation generation)) true
          (do (swap! (:state manager) update-in [:metrics :dropped-input-events] (fnil inc 0))
              (when (:source-id event) (swap! (:overflow-sources run) conj (:source-id event))) false))))))

(defn ingest!
  "Enqueue captured data. Returns false on a stopped/full boundary; never blocks
  a device listener."
  [manager event]
  (if-let [run (:active @(:state manager))] (queue! manager run event) false))

(defn clock-at
  "Selected external clock projection for the next owner frame. Manual selection
  returns clock nil so this boundary cannot overwrite the host's manual transport."
  [manager at-ms]
  (let [{:keys [config clock]} @(:state manager)
        result (clock/snapshot clock at-ms)]
    (cond-> result
      (= :manual (:selected-source result)) (assoc :clock nil)
      (= (get-in config [:link :source-id]) (:selected-source result))
      (assoc :follow-transport? (get-in config [:link :follow-transport?])))))

(defn apply-clock! [manager run event]
  (let [result (locking (:lock manager)
                 (let [result (clock/apply-event (:clock @(:state manager)) event)]
                   (when (:accepted? result) (swap! (:state manager) assoc :clock (:state result))) result))]
    (when (:accepted? result)
      (emit! manager run {:type :sync/clock :snapshot (clock-at manager ((get-in manager [:options :now-ms])))}))))

(defn commands! [manager run commands]
  (when (seq commands)
    (if-let [handler (:commands! (run-callbacks run))]
      (try (when (= false (handler commands)) (swap! (:state manager) update-in [:metrics :dropped-commands] (fnil + 0) (count commands)))
           (catch Exception error (swap! (:state manager) assoc :last-error (error-data error))))
      (emit! manager run {:type :sync/control-unavailable :commands commands}))))

(defn enqueue-io! [manager run task]
  (let [generation (or *input-generation* @(:binding-generation run))]
   (try (.execute ^ThreadPoolExecutor (:io run)
                  ^Runnable (fn [] (when (= generation @(:binding-generation run))
                                    (binding [*input-generation* generation] (task))))) true
       (catch RejectedExecutionException _
         (swap! (:state manager) update-in [:metrics :rejected-io] (fnil inc 0)) false))))

(defn flush!
  "Wait for earlier event-owner work only; outbound IO has separate execution
  acknowledgements. Useful to synchronize injected tests and REPL admission."
  ([manager] (flush! manager 1000))
  ([manager timeout-ms]
   (let [done (promise)]
     (and (ingest! manager {:type :barrier :promise done}) (true? (deref done timeout-ms false))))))

(ns afterglow.runtime.faults
  "Portable, bounded effect diagnostics. No clock, logging or mutable ownership."
  (:import [java.util.concurrent CancellationException]))

(defn recoverable?
  "User exceptions, assertions and linkage failures can be isolated. Cancellation,
  interruption and VM failures (including wrapped causes) remain owner failures."
  [error]
  (loop [cause error seen #{}]
    (cond
      (nil? cause) true
      (contains? seen cause) true
      (or (instance? InterruptedException cause) (instance? CancellationException cause)
          (instance? ThreadDeath cause) (instance? VirtualMachineError cause)) false
      (not (or (instance? Exception cause) (instance? AssertionError cause)
               (instance? LinkageError cause))) false
      :else (recur (.getCause ^Throwable cause) (conj seen cause)))))

(defn- text [value limit]
  (when (some? value) (let [s (str value)] (subs s 0 (min limit (count s))))))

(defn- location [error]
  (let [data (ex-data error)]
    (into {} (keep (fn [[key value]]
                     (cond
                       (and (= key :path) (vector? value))
                       [key (mapv #(if (or (keyword? %) (number? %)) % (text % 160)) (take 16 value))]
                       (or (keyword? value) (number? value) (string? value))
                       [key (if (string? value) (text value 256) value)])))
          (select-keys data [:type :path :file :line :column :target-id :attribute
                            :clojure.error/source :clojure.error/line :clojure.error/column :clojure.error/phase]))))

(defn diagnostic [frame instance version stage error]
  (when-not (recoverable? error) (throw error))
  (let [causes (take 4 (take-while some? (iterate #(.getCause ^Throwable %) error)))]
    (merge (select-keys frame [:show-id :epoch :time-ms :number])
           {:instance-id (:id instance) :cue-id (:cue-id instance)
            :effect-id (:effect-id instance) :effect-version version :stage stage
            :message (text (.getMessage ^Throwable (last causes)) 1024)
            :causes (mapv (fn [^Throwable cause]
                            {:class (.getName (class cause)) :message (text (.getMessage cause) 1024)
                             :location (location cause)
                             :trace (mapv (fn [^StackTraceElement entry]
                                            {:class (.getClassName entry) :method (.getMethodName entry)
                                             :file (.getFileName entry) :line (.getLineNumber entry)})
                                          (take 8 (.getStackTrace cause)))}) causes)})))

(defn event [type fault]
  (assoc fault :type type))

(defn record-events
  "Keep a bounded journal with monotonic sequence for durable reactive subscribers.
  A quarantined version emits once; explicit retries/new versions may emit again."
  [model events]
  (if-not (seq events) model
    (let [start (get-in model [:variables :runtime :event-sequence] 0)
          events (mapv #(assoc %1 :sequence %2) events (iterate inc (inc start)))]
      (-> model
          (assoc-in [:variables :runtime :event-sequence] (+ start (count events)))
          (update-in [:variables :runtime :events] #(vec (take-last 64 (into (vec %) events))))))))

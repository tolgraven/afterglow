(ns afterglow.bench-render
  "A stage microbenchmark of legacy assigner reduction and channel packing.
  Does not start a show, schedule workers, or send output to any device."
  (:require [afterglow.effects :as fx]
            [afterglow.effects.channel :as channel]
            [clojure.java.io :as io]
            [clojure.pprint :as pprint]
            [clojure.string :as str])
  (:import [java.lang.management ManagementFactory]
           [java.util Arrays]))

(def ^:private defaults {:heads [100 1000 10000] :warmup 30 :samples 100})

(defn- positive-integer [text]
  (let [value (Long/parseLong text)]
    (when-not (pos? value)
      (throw (ex-info "Benchmark counts must be positive integers." {:value text})))
    value))

(defn- options [args]
  (when (odd? (count args))
    (throw (ex-info "Options need values: --heads 100,1000,10000 --warmup 30 --samples 100" {})))
  (reduce (fn [result [option value]]
            (case option
              "--heads" (assoc result :heads (mapv positive-integer (str/split value #",")))
              "--warmup" (assoc result :warmup (positive-integer value))
              "--samples" (assoc result :samples (positive-integer value))
              (throw (ex-info "Unknown benchmark option." {:option option}))))
          defaults (partition 2 args)))

(defn- read-if-present [path]
  ;; Some containers expose proc/cgroup entries that the JVM cannot read.
  ;; Optional machine metadata must not prevent the benchmark from running.
  (try
    (when (.isFile (io/file path))
      (str/trim (slurp path)))
    (catch java.io.IOException _ nil)
    (catch SecurityException _ nil)))

(defn- environment []
  {:java-version (System/getProperty "java.version")
   :java-vm (System/getProperty "java.vm.name")
   :jvm-arguments (vec (.getInputArguments (ManagementFactory/getRuntimeMXBean)))
   :clojure-version (clojure-version)
   :os (System/getProperty "os.name")
   :os-version (System/getProperty "os.version")
   :architecture (System/getProperty "os.arch")
   :available-processors (.availableProcessors (Runtime/getRuntime))
   :max-heap-bytes (.maxMemory (Runtime/getRuntime))
   :cpu-model (some->> (read-if-present "/proc/cpuinfo")
                      (re-find #"(?m)^model name\s*:\s*(.+)$") second)
   :cgroup-cpu-max (read-if-present "/sys/fs/cgroup/cpu.max")
   :cgroup-memory-max (read-if-present "/sys/fs/cgroup/memory.max")
   :garbage-collectors (mapv #(.getName %) (ManagementFactory/getGarbageCollectorMXBeans))})

(defn- fixture [head-count]
  (let [channel-count (* 4 head-count)
        universe-count (quot (+ channel-count 511) 512)
        buffers (into {} (for [universe (range 1 (inc universe-count))]
                           [universe (byte-array 512)]))
        groups (mapv (fn [index]
                       (let [target {:universe (inc (quot index 512))
                                     :address (inc (mod index 512))
                                     :index (mod index 512)}
                             base (mod (+ (nth [16 64 128 32] (mod index 4))
                                          (quot index 4)) 256)]
                         [(channel/build-channel-assigner target (fn [_ _ _ _] base))
                          (channel/build-channel-assigner target (fn [_ _ _ previous]
                                                                   (min 255 (+ 20 previous))))
                          (channel/build-channel-assigner target (fn [_ _ _ previous]
                                                                   (* 0.75 previous)))]))
                     (range channel-count))]
    {:buffers buffers :groups groups :channels channel-count :universes universe-count}))

(defn- render-stage! [{:keys [buffers groups]}]
  ;; Fixed context: this benchmark excludes snapshots, effect generation,
  ;; assigner grouping, color conversion, movement, and hardware transport.
  (doseq [^bytes buffer (vals buffers)]
    (Arrays/fill buffer (byte 0)))
  (doseq [assigners groups]
    (fx/resolve-assignment (fx/run-assigners {} {:instant 0} assigners) {} {:instant 0} buffers)))

(defn- checksum [buffers]
  (reduce + 0 (for [^bytes buffer (vals buffers), value buffer]
                (bit-and value 0xff))))

(defn- percentile [sorted-samples fraction]
  ;; Nearest rank. With only 100 samples p99 is the second-largest sample;
  ;; these observations are not a stable latency guarantee.
  (nth sorted-samples (dec (max 1 (long (Math/ceil (* fraction (count sorted-samples))))))))

(defn- benchmark [head-count {:keys [warmup samples]}]
  (let [fixture (fixture head-count)]
    (dotimes [_ warmup] (render-stage! fixture))
    (let [expected-checksum (checksum (:buffers fixture))
          elapsed-ms (loop [remaining samples, times []]
                       (if (zero? remaining)
                         times
                         (let [started (System/nanoTime)]
                           (render-stage! fixture)
                           (let [elapsed (/ (- (System/nanoTime) started) 1.0e6)]
                             ;; Outside the timed section, ensure every observed
                             ;; output is consumed and identical to warmup output.
                             (when-not (= expected-checksum (checksum (:buffers fixture)))
                               (throw (ex-info "Output changed across identical benchmark inputs."
                                               {:heads head-count})))
                             (recur (dec remaining) (conj times elapsed))))))
          ordered (vec (sort elapsed-ms))]
      {:heads head-count :layout :rgbw :channels (:channels fixture)
       :universes (:universes fixture) :assigners-per-channel 3
       :warmup-frames warmup :measured-frames samples
       :checksum expected-checksum
       :milliseconds {:min (first ordered)
                      :p50 (percentile ordered 0.50)
                      :p95 (percentile ordered 0.95)
                      :p99 (percentile ordered 0.99)
                      :max (peek ordered)}
       :samples-ms elapsed-ms})))

(defn -main [& args]
  (try
    (let [config (options args)]
      (pprint/pprint
       {:benchmark :legacy-assignment-and-channel-packing
        :version 1
        :source-revision (System/getProperty "afterglow.benchmark.revision" "unknown")
        :measured-at (str (java.time.Instant/now))
        :environment (environment)
        :timed [:clear-local-buffers :run-prebuilt-assigners :resolve-channel-assignments]
        :excluded [:effect-generation :assigner-grouping :workers :color-conversion
                   :geometry :movement :network :art-net :gpu :checksum]
        :allocation-measurement :not-measured
        :results (mapv #(benchmark % config) (:heads config))}))
    (finally (shutdown-agents))))

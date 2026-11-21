(ns afterglow.bench-backend
  "Benchmarks owned frame resolution and comparable legacy/new channel packing.
  Requires a legacy classpath when --legacy true is supplied; no hardware I/O."
  (:require [afterglow.render.frame :as frame]
            [afterglow.render.ir :as ir]
            [clojure.pprint :as pprint]
            [clojure.string :as str])
  (:import [java.util Arrays]
           [java.lang.management ManagementFactory]))

(defn- config [args]
  (when (odd? (count args)) (throw (ex-info "Every option requires a value" {})))
  (reduce (fn [result [option value]]
            (case option
              "--heads" (assoc result :heads (mapv #(Long/parseLong %) (str/split value #",")))
              "--warmup" (assoc result :warmup (Long/parseLong value))
              "--samples" (assoc result :samples (Long/parseLong value))
              "--stages" (assoc result :stages (set (map keyword (str/split value #","))))
              "--legacy" (if (#{"true" "false"} value)
                           (assoc result :legacy? (= value "true"))
                           (throw (ex-info "--legacy expects true or false" {})))
              (throw (ex-info "Unknown option" {:option option}))))
          {:heads [100 1000 10000] :warmup 30 :samples 100 :legacy? false}
          (partition 2 args)))

(defn- buffers [universes]
  (into (sorted-map) (map #(vector % (byte-array 512)) universes)))

(defn- clear! [buffers]
  (doseq [^bytes buffer (vals buffers)] (Arrays/fill buffer (byte 0))))

(defn- same-buffers? [a b]
  (and (= (set (keys a)) (set (keys b)))
       (every? (fn [[universe ^bytes bytes]]
                 (Arrays/equals bytes ^bytes (get b universe))) a)))

(defn- checksum [buffers]
  (reduce + (for [^bytes buffer (vals buffers), value buffer] (bit-and 255 value))))

(defn- corpus [heads]
  (let [fixtures (mapv (fn [i]
                         {:id i :position [(double i) 0 0]
                          :universe (inc (quot (* i 4) 512))
                          :address (inc (mod (* i 4) 512))
                          :channels {:red 1 :green 2 :blue 3 :white 4}}) (range heads))
        patch (frame/compile-patch fixtures)
        assignments (vec (for [i (range heads), [offset attribute] (map-indexed vector [:red :green :blue :white])]
                           {:target-id i :attribute attribute :blend :replace
                            :value (/ (double (mod (+ (* 4 i) offset) 256)) 255.0)}))
        packing (mapv (fn [{:keys [target-id attribute value]}]
                        (let [channel (get-in patch [:by-id target-id :compiled-channels attribute])
                              [universe index] (:coarse channel)]
                          {:channel channel :value value
                           :legacy {:universe universe :index index}})) assignments)]
    {:patch patch :assignments assignments :packing packing}))

(defn- measure [label run expected {:keys [warmup samples stages]}]
  (when (or (nil? stages) (contains? stages label))
    (dotimes [_ warmup]
      (when-not (same-buffers? expected (run))
        (throw (ex-info "Benchmark output mismatch" {:stage label}))))
    (let [bean (ManagementFactory/getThreadMXBean)
          allocation-supported? (and (instance? com.sun.management.ThreadMXBean bean)
                                     (.isThreadAllocatedMemorySupported ^com.sun.management.ThreadMXBean bean))
          thread-id (.getId (Thread/currentThread))
          cpu-supported? (and (.isCurrentThreadCpuTimeSupported bean) (.isThreadCpuTimeEnabled bean))
          cpu-time (fn [] (when cpu-supported? (.getCurrentThreadCpuTime bean)))
          allocated (fn [] (when allocation-supported?
                            (.getThreadAllocatedBytes ^com.sun.management.ThreadMXBean bean thread-id)))
          observations (mapv (fn [_]
                          (let [bytes-before (allocated), cpu-before (cpu-time)
                                start (System/nanoTime), result (run)
                                ms (/ (- (System/nanoTime) start) 1.0e6)
                                cpu-after (cpu-time), bytes-after (allocated)]
                            (when-not (same-buffers? expected result)
                              (throw (ex-info "Benchmark output mismatch" {:stage label})))
                            {:ms ms :cpu-ms (when (and cpu-before cpu-after) (/ (- cpu-after cpu-before) 1.0e6)) :allocated (when (and bytes-before bytes-after) (- bytes-after bytes-before))})) (range samples))
          timings (mapv :ms observations)
          percentile (fn [ordered p] (nth ordered (dec (max 1 (long (Math/ceil (* p samples)))))))
          summarize (fn [values] (let [ordered (vec (sort values))]
                                   {:p50 (percentile ordered 0.5) :p95 (percentile ordered 0.95)
                                    :p99 (percentile ordered 0.99) :min (first ordered) :max (peek ordered)}))]
      {:stage label :warmup warmup :samples samples :checksum (checksum expected)
       :milliseconds (summarize timings)
       :current-thread-cpu-milliseconds (when cpu-supported? (summarize (map :cpu-ms observations)))
       :allocated-bytes-per-frame (when allocation-supported? (mapv :allocated observations))
       :samples-ms timings :samples-current-thread-cpu-ms (when cpu-supported? (mapv :cpu-ms observations))})))

(defn- benchmark [heads options legacy-pack]
  (let [{:keys [patch assignments packing]} (corpus heads)
        batch {:count heads :target-ids (:target-order patch)
               :outputs (into {} (map-indexed
                                  (fn [component attribute]
                                    [attribute {:type :number :components 1
                                                :values (double-array
                                                         (map (fn [head] (:value (nth assignments (+ (* head 4) component))))
                                                              (range heads)))}]) [:red :green :blue :white]))}
        expressions {:color {:op :vec3 :args [{:op :multiply :args [{:op :const :value 0.5}
                                                                  {:op :add :args [{:op :const :value 1.0}
                                                                                  {:op :sin :args [{:op :add :args [{:op :multiply :args [{:op :position :axis :x} {:op :const :value 0.05}]}
                                                                                                                  {:op :multiply :args [{:op :time} {:op :const :value 0.001}]}]}]}]}]}
                                                {:op :param :key :level} {:op :const :value 0.25}]}
                     :white {:op :const :value 0.1}}
        expression-plan (ir/compile-batch expressions)
        positions (mapv :position (:fixtures patch))
        environment {:elapsed-ms 1250.0 :params {:level 0.5}}
        scalar-expressions (into {} (map (fn [[attribute expression]] [attribute (ir/compile-expression expression)]) expressions))
        scalar-assignments (vec (for [fixture (:fixtures patch), [attribute evaluate] scalar-expressions]
                                 {:target-id (:id fixture) :attribute attribute :blend :replace
                                  :value (evaluate (assoc environment :position (:position fixture)))}))
        expression-expected (:universes (frame/resolve-frame patch scalar-assignments))
        expected (:universes (frame/resolve-frame patch assignments))
        packed (buffers (:universes patch))
        legacy (buffers (:universes patch))
        new-packing (fn []
                      (clear! packed)
                      (doseq [{:keys [channel value]} packing] (frame/pack-value! packed channel value))
                      packed)
        old-packing (fn []
                      (clear! legacy)
                      (doseq [{:keys [value] old-channel :legacy} packing]
                        (legacy-pack legacy old-channel (* value 255.0)))
                      legacy)]
    ;; Compare against actual legacy implementation, not only self-generated goldens.
    (when (and legacy-pack (not (same-buffers? expected (old-packing))))
      (throw (ex-info "New frame differs from legacy channel output" {:heads heads})))
    {:heads heads :channels (* 4 heads) :universes (count (:universes patch))
     :results (filterv some? (cond-> [(measure :new-frame-resolution-and-packing
                               #(:universes (frame/resolve-frame patch assignments)) expected options)
                       (measure :new-transport-frame-resolution-and-packing
                                #(:universes (frame/resolve-frame patch assignments {:include-values? false})) expected options)
                       (measure :new-frame-with-compact-preview
                                #(:universes (frame/resolve-frame patch assignments {:include-values? false :compact-values? true})) expected options)
                       (measure :typed-batch-resolution-with-compact-preview
                                #(:universes (frame/resolve-batches patch [batch] {:include-values? false :compact-values? true})) expected options)
                       (measure :ir-spatial-effect-through-dmx-with-compact-preview
                                #(let [calculated (assoc (ir/evaluate-batch expression-plan environment positions)
                                                         :target-ids (:target-order patch))]
                                   (:universes (frame/resolve-batches patch [calculated]
                                                                     {:include-values? false :compact-values? true})))
                                expression-expected options)
                       (measure :new-precompiled-channel-packing new-packing expected options)]
                legacy-pack (conj (measure :legacy-channel-packing old-packing expected options))))}))

(defn -main [& args]
  (try
    (let [{:keys [heads warmup samples legacy?] :as options} (config args)]
      (when-not (and (seq heads) (every? pos-int? heads) (pos-int? warmup) (pos-int? samples))
        (throw (ex-info "Counts must be positive integers" {:options options})))
      (let [legacy-pack (when legacy? (requiring-resolve 'afterglow.effects.channel/apply-channel-value))]
        (pprint/pprint
         {:benchmark :functional-render-backend :version 1
          :measured-at (str (java.time.Instant/now))
          :source-revision (System/getProperty "afterglow.benchmark.revision" "working-tree")
          :environment {:java-version (System/getProperty "java.version")
                        :clojure-version (clojure-version)
                        :os (System/getProperty "os.name") :architecture (System/getProperty "os.arch")
                        :processors (.availableProcessors (Runtime/getRuntime))
                        :heap-bytes (.maxMemory (Runtime/getRuntime))
                        :jvm-arguments (vec (.getInputArguments (ManagementFactory/getRuntimeMXBean)))}
          :notes ["Only the two channel-packing stages are directly comparable."
                  "Full frame stage also validates/reduces assignments, resolves RGBW/dimmer values and allocates fresh output."
                  "Packing stages reuse preallocated arrays and clear them each iteration."
                  "Every measured output is byte-compared outside its timed interval."
                  "Thread-allocated bytes cover the synchronous measured stage; output comparisons are outside measurement."
                  "Current-thread CPU time helps identify wall-clock contention; it excludes other threads and cannot establish complete-frame deadlines."
                  "The IR-spatial stage evaluates explicit position/time expressions and resolves resulting typed batches through DMX packing, including compact preview. Its corpus differs from the packing comparison."
                  "No GPU, network transport, control/registry scheduling, worker allocations, or complete-show latency is measured."]
          :results (mapv #(benchmark % options legacy-pack) heads)})))
    (finally (shutdown-agents))))

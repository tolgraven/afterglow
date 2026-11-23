(require '[tolglow.perf.weighted-venue :as venue] '[tolglow.bench-show :as bench] '[tolglow.show :as show]
         '[afterglow.render.coverage :as coverage] '[afterglow.render.gpu.expressions :as gpu] '[afterglow.render.gpu.session :as session] '[afterglow.runtime.reuse :as reuse] '[afterglow.spatial.beam :as beam] '[afterglow.spatial.field :as field] '[afterglow.spatial.geometry :as geometry] '[afterglow.time :as time]
         '[clojure.edn :as edn] '[clojure.string :as str])
(import '[java.lang.management ManagementFactory] '[java.security MessageDigest] '[java.util HexFormat]
        '[java.time Instant Duration] '[jdk.jfr Recording] '[jdk.jfr.consumer RecordingFile]
        '[java.nio.file Paths] '[java.io File])
(load-file (System/getenv "VENUE_MATERIAL_FILE"))
(defn old-vec3? [v] (and (vector? v) (= 3 (count v)) (every? time/finite-number? v)))
(def ^:dynamic *stages* nil)
(def stages
  {'afterglow.spatial/advance :physics
   'tolglow.spatial/advance :spatial
   'tolglow.spatial.cues/frame-fields :weighted-fields
   'afterglow.spatial.field/sample-volume :field
   'afterglow.runtime.engine/advance :engine
   'afterglow.render.frame/resolve-contributions :render
   'afterglow.render.layers/compose :layers})
(defn stage-wrapper [f stage]
  (fn [& args]
    (if-not *stages* (apply f args)
      (let [start (System/nanoTime)]
        (try (apply f args)
             (finally (swap! *stages* update stage (fnil + 0.0)
                             (/ (- (System/nanoTime) start) 1e6))))))))
(def wrappers
  (into {} (keep (fn [[sym stage]]
                   (when-let [v (resolve sym)] [v (stage-wrapper @v stage)]))) stages))

(defn epoch-ns [^Instant x]
  (+ (* (.getEpochSecond x) 1000000000) (.getNano x)))
(defn proc-text [path]
  (with-open [stream (java.io.FileInputStream. ^String path)]
    (String. (.readNBytes stream 4096) java.nio.charset.StandardCharsets/UTF_8)))
(defn clock-sample []
  (let [[cpu waiting] (map parse-long (str/split (str/trim (proc-text "/proc/thread-self/schedstat")) #"\s+"))
        stats (->> (str/split-lines (proc-text "/sys/fs/cgroup/cpu.stat"))
                   (map #(str/split % #" ")) (into {}))]
    {:main-cpu cpu :runqueue waiting :cgroup-throttled-ms (* 1000 (parse-long (stats "throttled_usec")))}))
(defn observations [f counters]
  (let [a (clock-sample) start-bytes ((:allocated counters)) start-cpu ((:cpu counters))
        begin (epoch-ns (Instant/now)) mono (System/nanoTime)
        stages (atom {}) result (binding [*stages* stages] (f)) wall (- (System/nanoTime) mono) end (epoch-ns (Instant/now))
        cpu-ms (/ (- ((:cpu counters)) start-cpu) 1e6) bytes (- ((:allocated counters)) start-bytes)
        b (clock-sample)]
    {:frame result :metrics (merge {:start begin :end end :ms (/ wall 1e6) :cpu-ms cpu-ms :bytes bytes}
                                   @stages (:stages-ms result) (update-vals (merge-with - b a) #(/ % 1e6)))}))
(defn pauses [path]
  (for [event (RecordingFile/readAllEvents path) :when (= "jdk.GCPhasePause" (.getName (.getEventType event)))]
    [(epoch-ns (.getStartTime event)) (epoch-ns (.getEndTime event))]))
(defn with-pauses [events {:keys [start end] :as row}]
  (assoc row :gc-pause-ms (/ (reduce + (map (fn [[a b]] (max 0 (- (min b end) (max a start)))) events)) 1e6)))
(defn layers [model]
  (reduce (fn [m i]
            (let [id (keyword (str "wash-" i))
                  d {:id id :version 1 :outputs {:color [(/ (inc i) 21.0) 0.18 0.37] :white (/ (inc i) 20.0)}}]
              (-> m (bench/command [id :publish] {:op :registry/publish :kind :effects :definition d})
                  (bench/command [id :cue] {:op :cue/put :cue {:id id :effect-id id :priority (+ 20 i)}})
                  (bench/command [id :play] {:op :cue/launch :cue-id id})))) model
          (range (parse-long (or (System/getenv "VENUE_WASHES") "8")))))

(defn rig-and-hosts [pixels]
  (let [{:keys [model preview-indices]} (#'venue/venue pixels)
        shapes (venue/volumes 4 #{:position :beam} 0.0)
        model (#'venue/seed-model (layers (mixed-chart-model model)) shapes)
        owners (into {} (map (juxt :cue-id :id)) (vals (:instances model)))]
    {:ids (mapv #(owners (str "venue-field-" %)) (range 4))
     :preview-indices preview-indices
     :hosts (let [options (when-let [ms (System/getenv "VENUE_GPU_MS")]
                               {:compute-backend :native-gpu :movement-backend (if (= "cpu" (System/getenv "VENUE_MOVEMENT")) :cpu :native-gpu) :gpu-budget-ms (parse-long ms) :gpu-options {:max-programs 16 :timeout-ms 10000}})
                  create! show/create-runtime]
              (with-redefs [show/create-runtime #(create! (cond-> (merge % options)
                                                          (System/getenv "VENUE_WORKER_MS")
                                                          (assoc :worker-timeout-ms (parse-long (System/getenv "VENUE_WORKER_MS")))))]
                [(#'venue/new-show model false) (#'venue/new-show model false)]))
     :digest (MessageDigest/getInstance "SHA-256")}))

(defn previous-evaluator [owner stats program]
  (reuse/evaluator {:pure? true :inputs [[:uniforms]]}
    (fn [{:keys [uniforms]}]
      (let [batch (gpu/run-program! owner program uniforms)]
        (when (pos? (:count program)) (swap! stats update :draws inc))
        batch))))

(defn advance-lane [{:keys [hosts ids preview-indices]} lane frame-number]
  (let [advance #(#'venue/host-step (hosts lane) ids preview-indices frame-number)]
    (if (= lane 0)
      (with-redefs-fn {#'session/program-evaluator previous-evaluator} advance)
      (advance))))

(defn capture-pair [{:keys [digest] :as rig} counters frame-number]
  (let [order (if (even? frame-number) [0 1] [1 0])
        capture (fn [lane]
                  (let [run #(advance-lane rig lane frame-number)]
                    [lane (if counters (observations run counters) {:frame (run)})]))
        results (into {} (map capture) order)
        reference (get-in results [0 :frame])]
    (let [actual (get-in results [1 :frame])]
      (try (bench/check! reference actual)
           (catch Exception e
             (let [changed (for [[u [^bytes a ^bytes b]] (map-indexed vector (map vector (:packets reference) (:packets actual)))
                                 i (range (alength a)) :when (not= (aget a i) (aget b i))]
                             [u i (bit-and 255 (aget a i)) (bit-and 255 (aget b i))])
                   differences (keep-indexed (fn [i x] (let [y (nth (:preview actual) i)]
                                                       (when (not= x y) [i x y])))
                                             (:preview reference))]
               (spit (str (first *command-line-args*) ".mismatch")
                     (pr-str {:frame frame-number :packets-changed (count changed) :examples (take 8 changed)
                              :previews (take 4 differences)
                              :status (mapv (fn [{:keys [runtime]}]
                                               (select-keys (:status (show/snapshot runtime)) [:compute :movement]))
                                             (:hosts rig))})))
             (throw e))))
    (doseq [^bytes packet (:packets reference)]
      (.update ^MessageDigest digest packet))
    (mapv (fn [lane] (assoc (get-in results [lane :metrics])
                           :i frame-number :lane lane :order (.indexOf order lane)))
          [0 1])))

(defn record-frames [rig path warmup samples]
  (let [counters (#'bench/worker-counters)
        measure #(vec (mapcat (partial capture-pair rig counters) (range warmup (+ warmup samples))))]
    (with-open [recording (Recording.)]
      (.enable recording "jdk.GCPhasePause")
      (.start recording)
      (let [rows (with-redefs-fn wrappers measure)]
        (.stop recording)
        (.dump recording path)
        (let [events (vec (pauses path))]
          (mapv (partial with-pauses events) rows))))))

(defn traffic [rig i]
  (let [draw gpu/run-program!
        measure (fn [lane]
                  (let [calls (atom {:draws 0 :vertices 0 :readback-bytes 0})
                        observe (fn [owner program inputs]
                                  (let [v (:vertices program)]
                                    (swap! calls (fn [x] (-> x (update :draws inc) (update :vertices + v)
                                                             (update :readback-bytes + (* 4 v (:stride (:plan program))))))))
                                  (draw owner program inputs))]
                    (with-redefs [gpu/run-program! observe] {:frame (advance-lane rig lane i) :calls @calls})))
        [full broadcast] (mapv measure (range 2))]
    (bench/check! (:frame full) (:frame broadcast))
    [(:calls full) (:calls broadcast)]))

(defn replay [output warmup samples]
  (let [path (Paths/get (str output ".jfr") (make-array String 0))
        primer (rig-and-hosts 1000)
        _ (try (dotimes [i 4] (capture-pair primer nil i))
               (finally (doseq [host (:hosts primer)] (show/stop! (:runtime host)))))
        rig (rig-and-hosts (parse-long (or (System/getenv "VENUE_PIXELS") "20000")))]
    (try
      (dotimes [i warmup] (capture-pair rig nil i))
      (let [rows (record-frames rig path warmup samples)]
        (spit output (pr-str {:mode "optics" :warmup warmup :samples samples
                              :artdmx-sha256 (.formatHex (HexFormat/of) (.digest ^MessageDigest (:digest rig)))
                              :rows rows :traffic (traffic rig (+ warmup samples))
                              :backends (mapv (fn [{:keys [runtime]}] (select-keys (:status (show/snapshot runtime)) [:compute :movement])) (:hosts rig))})))
      (finally
        (doseq [host (:hosts rig)] (show/stop! (:runtime host)))
        (shutdown-agents)))))

(defn sample-copy-traffic [rig number]
  (let [by-array (java.util.Collections/synchronizedMap (java.util.IdentityHashMap.))
        counts (atom {:expansions 0 :allocated-components 0 :expanded-columns 0
                      :matched-columns 0 :matched-components 0 :covered-components 0})
        expand gpu/expand-uniform
        observe-expansion (fn [sample n]
                            (let [expanded (expand sample n)]
                              (swap! counts update :expansions inc)
                              (doseq [[_ {:keys [components values]}] (:outputs expanded)]
                                (.put by-array values true)
                                (swap! counts #(-> % (update :expanded-columns inc)
                                                   (update :allocated-components + (* n components)))))
                              expanded))
        plan coverage/plan
        observe-coverage (fn [blocks]
                           (let [planned (plan blocks)]
                             (doseq [{:keys [compiled]} planned
                                     {:keys [values components] :as column} (:columns compiled)
                                     :when (.containsKey by-array values)]
                               (swap! counts #(-> % (update :matched-columns inc)
                                                  (update :matched-components + (* (count (:target-ids compiled)) components))
                                                  (update :covered-components + (* (::coverage/validate-prefix column 0) components)))))
                             planned))
        reference (advance-lane rig 0 number)
        candidate (with-redefs [gpu/expand-uniform observe-expansion coverage/plan observe-coverage]
                    (advance-lane rig 1 number))]
    (bench/check! reference candidate)
    @counts))
(let [[out] *command-line-args*
      primer (rig-and-hosts 1000)]
  (try (dotimes [n 3] (capture-pair primer nil n))
       (finally (doseq [h (:hosts primer)] (show/stop! (:runtime h)))))
  (let [rig (rig-and-hosts 20000)]
    (try (dotimes [n 2] (capture-pair rig nil n))
         (spit out (pr-str {:rows (mapv #(sample-copy-traffic rig %) [2 3 4])
                            :targets 20064 :washes 8 :movers 64}))
         (finally (doseq [h (:hosts rig)] (show/stop! (:runtime h))) (shutdown-agents)))))

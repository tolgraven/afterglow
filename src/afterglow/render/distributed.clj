(ns afterglow.render.distributed
  "A bounded pool of paired remote numerical workers. Jobs return typed fields
  for one current frame. Only the caller owns fixture packing and output."
  (:require [afterglow.render.ir :as ir]
            [afterglow.render.verified :as verified])
  (:import [java.nio ByteBuffer ByteOrder]
           [java.util UUID]
           [java.util.concurrent CompletableFuture TimeUnit TimeoutException]))

(def verification-policies
  "Host capabilities for separately authenticated guest admission."
  #{:full :redundant})

(def ^:private max-heads 262144)
(def ^:private max-floats 1048576)
(def ^:private max-peers 16)
(def ^:private max-resident 4)
(defn- token [] (str (UUID/randomUUID)))
(defn- finite-float [x]
  (when-not (and (number? x) (Float/isFinite (unchecked-float x)))
    (throw (ex-info "Expected a finite float32 input" {})))
  (unchecked-float x))

(defn- buffer [data] (.order (ByteBuffer/wrap ^bytes data) ByteOrder/LITTLE_ENDIAN))

(defn- pack-points [points width n fallback]
  (let [data (byte-array (* n width Float/BYTES))
        dst (.asFloatBuffer (buffer data))]
    (if (instance? double/1 points)
      (dotimes [i (* n width)] (.put dst (finite-float (aget ^doubles points i))))
      (dotimes [i n]
        (let [p (or (nth points i) (when fallback (fallback i)))]
          (when-not (= (count p) width) (throw (ex-info "Wrong coordinate width" {:head i})))
          (doseq [x p] (.put dst (finite-float x))))))
    data))

(defn- packet [expressions positions uvs n]
  (let [xy (fn [i] (if (instance? double/1 positions)
                     [(aget ^doubles positions (* i 3)) (aget ^doubles positions (inc (* i 3)))]
                     (subvec (nth positions i) 0 2)))
        plan (ir/emit-glsl-batch expressions {:surface-uv? (some? uvs)})]
    (cond-> {:op :prepare :id (token) :plan plan :positions (pack-points positions 3 n nil)}
      (and uvs (:surface-uv (:inputs plan))) (assoc :surface-uvs (pack-points uvs 2 n xy)))))

(defn prepare-group
  ([expressions positions cpu-plan] (prepare-group expressions positions cpu-plan nil))
  ([expressions positions cpu-plan uvs]
   (let [positions (if (instance? double/1 positions) (aclone ^doubles positions) positions)
         uvs (if (instance? double/1 uvs) (aclone ^doubles uvs) uvs)
         cpu {:expressions expressions :positions positions :surface-uvs uvs :cpu-plan cpu-plan}
         n (if (instance? double/1 positions) (quot (alength ^doubles positions) 3) (count positions))]
     (if-not (<= 1 n max-heads) cpu
       (try
         (assoc cpu :count n :packet (packet expressions positions uvs n))
         (catch Exception error
           (assoc cpu :preparation-error {:type :unsupported-remote-group :message (.getMessage error)})))))))

(defn create []
  {:peers (atom {}) :lock (Object.)
   :state (atom {:closed? false :completed 0 :missed 0 :rejected 0})})

(defn connected?
  "Whether a transport still owns an admitted worker in this pool."
  [pool id]
  (contains? @(:peers pool) id))

(defn status [pool]
  (locking (:lock pool)
    (assoc @(:state pool) :workers (count @(:peers pool))
           :busy (count (filter :job (vals @(:peers pool)))))))

(defn connect! [pool caps send!]
  (let [capacity (:max-result-floats caps)]
    (when-not (and (pos-int? capacity) (fn? send!)
                   (or (nil? (:verification caps)) (contains? verification-policies (:verification caps)))
                   (or (not= :redundant (:verification caps))
                       (and (string? (:subject caps)) (<= 1 (count (:subject caps)) 128))))
      (throw (ex-info "Missing worker capability or transport" {})))
    (locking (:lock pool)
      (when (or (:closed? @(:state pool)) (>= (count @(:peers pool)) max-peers))
        (throw (ex-info "Render pool is closed or full" {})))
      (let [id (token)]
        (swap! (:peers pool) assoc id {:send! send! :capacity (min max-floats capacity) :ready []
                                      :verification (:verification caps) :subject (:subject caps)})
        id))))

(defn disconnect! [pool id]
  (locking (:lock pool)
    (when-let [p (get @(:peers pool) id)]
      (swap! (:peers pool) dissoc id)
      (when-let [done (get-in p [:job :done])] (.complete ^CompletableFuture done nil)))))

(defn close! [pool]
  (locking (:lock pool)
    (swap! (:state pool) assoc :closed? true)
    (doseq [id (keys @(:peers pool))] (disconnect! pool id))))

(defn receive! [pool id {:keys [op job values] program :id}]
  (locking (:lock pool)
    (when-let [{pending :preparing active :job :as peer} (get @(:peers pool) id)]
      (cond
        (and (= :ready op) pending (= program pending))
        (swap! (:peers pool) assoc id
               (-> peer (dissoc :preparing)
                   (update :ready #(vec (take-last max-resident (conj (filterv (partial not= program) %) program))))))

        (and (= :error op) program (nil? job))
        (if (= program pending)
          (do (swap! (:state pool) update :rejected inc)
              (swap! (:peers pool) update id #(-> % (dissoc :preparing) (assoc :unavailable program))))
          (swap! (:peers pool) update-in [id :ready] #(filterv (partial not= program) %)))

        (and active (= job (:id active)) (#{:result :error} op))
        (let [valid? (and (= op :result) (bytes? values) (= (* Float/BYTES (:floats active)) (alength ^bytes values)))]
          (if valid?
            (swap! (:peers pool) update id dissoc :job)
            (do (swap! (:state pool) update :rejected inc) (disconnect! pool id)))
          (.complete ^CompletableFuture (:done active) (when valid? values)))
        :else nil)))
  nil)

(defn- uniforms [{:keys [inputs uniforms]} env]
  (let [clock (fn [[key name]]
                (let [meter? (#{:beats-per-bar :bars-per-phrase} key)
                      x (finite-float (if meter? (get-in env [:meter key]) (get env key)))]
                  (when (and meter? (not (pos? x))) (throw (ex-info "Invalid meter" {:key key})))
                  [name [x]]))
        parameter (fn [[k {:keys [type name]}]]
                    (let [v (get-in env [:params k])
                          values (if (= type :number) [v] v)
                          width ({:number 1 :vec2 2 :vec3 3 :vec4 4} type)]
                      (when-not (and (vector? values) (= width (count values)))
                        (throw (ex-info "Invalid shader input" {:param k})))
                      [name (mapv finite-float values)]))]
    (into (into {} (map clock) (dissoc inputs :position :surface-uv)) (map parameter) uniforms)))

(defn- lanes [warm]
  (let [paired? #(= :redundant (:verification (val %)))
        singles (mapv vector (remove paired? warm))
        ;; A session with no independent witness goes through the full CPU check.
        pair (fn [[a b]] (if (and b (not= (:subject (val a)) (:subject (val b))))
                           [[a b]] (cond-> [[a]] b (conj [b]))))]
    (into singles (mapcat pair) (partition-all 2 (filter paired? warm)))))

(defn- assign! [pool workers offset n stride]
  (mapv (fn [[id peer]]
          (let [job {:id (token) :peer id :send! (:send! peer) :done (CompletableFuture.)
                     :verification (:verification peer) :start offset :count n :floats (* stride n)}]
            (swap! (:peers pool) assoc-in [id :job] job)
            job)) workers))

(defn- lease [pool group]
  (let [{program :id :keys [plan] :as setup} (:packet group)
        n (:count group) stride (:stride plan)]
    (locking (:lock pool)
      (let [peers @(:peers pool)
            idle (remove (fn [[_ p]] (or (:job p) (:preparing p))) (sort-by key peers))
            warm (vec (filter (fn [[_ p]] (some #{program} (:ready p))) idle))
            cold (remove (fn [[_ p]] (or (= program (:unavailable p)) (some #{program} (:ready p)))) idle)
            preps (mapv (fn [[id peer]]
                          (swap! (:peers pool) assoc-in [id :preparing] program)
                          [id (:send! peer) setup]) cold)
            groups (lanes warm)
            capacities (mapv (fn [lane] (quot (reduce min (map #(:capacity (val %)) lane)) stride)) groups)]
        {:preps preps
         :jobs (when (<= n (reduce + 0 capacities))
                 (loop [remaining n offset 0 index 0 jobs []]
                   (if (zero? remaining) jobs
                     (let [lane (groups index)
                           equally (long (Math/ceil (/ (double remaining) (- (count groups) index))))
                           needed (- remaining (reduce + 0 (subvec capacities (inc index))))
                           cnt (min remaining (capacities index) (max equally needed))]
                       (if (zero? cnt) (recur remaining offset (inc index) jobs)
                         (recur (- remaining cnt) (+ offset cnt) (inc index)
                                (into jobs (assign! pool lane offset cnt stride))))))))}))))

(defn- send-packet! [pool peer send! packet]
  (try (send! packet)
       (catch Exception _ (disconnect! pool peer))))

(defn- collect [jobs deadline]
  (mapv (fn [{:keys [done]}]
          (let [ns-left (- deadline (System/nanoTime))]
            (when (pos? ns-left)
              (try (.get ^CompletableFuture done ns-left TimeUnit/NANOSECONDS)
                   (catch TimeoutException _ nil)
                   (catch InterruptedException _
                     (.interrupt (Thread/currentThread))
                     nil))))) jobs))

(defn- unpack [plan n jobs chunks]
  (let [outputs (into {} (map (fn [{:keys [attribute components type]}]
                                [attribute {:type type :components components :values (double-array (* n components))}]))
                      (:outputs plan))]
    (doseq [[{:keys [start count]} chunk] (map vector jobs chunks)]
      (if (map? chunk)
        (doseq [[attribute {:keys [components values]}] (:outputs chunk)]
          (System/arraycopy values 0 (get-in outputs [attribute :values]) (int (* start components)) (alength ^doubles values)))
        (let [floats (.asFloatBuffer (buffer chunk))]
          (dotimes [i count]
            (doseq [{:keys [attribute components]} (:outputs plan)]
              (let [^doubles target (:values (outputs attribute)) dest (* (+ start i) components)]
                (dotimes [j components]
                  (let [v (.get floats)]
                    (when-not (Float/isFinite v) (throw (ex-info "Nonfinite remote output" {:attribute attribute})))
                    (aset-double target (+ dest j) (double v))))))))))
    {:count n :outputs outputs}))

(defn- reject-peer! [pool job]
  (swap! (:state pool) update :rejected inc)
  (disconnect! pool (:peer job))
  nil)

(defn- checked-slices [pool group env jobs chunks]
  (let [verify (fn [[job data]] (or (verified/readback group env job data) (reject-peer! pool job)))
        check (fn [[[job a :as first-copy] [_ b] :as copies]]
                [job (cond
                       (nil? (:verification job)) a
                       (nil? b) (verify first-copy)
                       (verified/agree? group env job a b) a
                       :else (do (doseq [copy copies] (verify copy)) nil))])]
    (mapv check (partition-by (comp :start first) (map vector jobs chunks)))))

(defn evaluate!
  "Return the joined field batch within the frame deadline, or nil for local evaluation.
  A transport must enqueue without blocking. Never wait for program preparation."
  [pool group env deadline]
  (when (and (:packet group) (seq @(:peers pool)) (< (System/nanoTime) deadline))
    (let [{:keys [id plan]} (:packet group)
          values (uniforms plan env)
          {:keys [preps jobs]} (lease pool group)]
      (doseq [[peer send! setup] preps] (send-packet! pool peer send! setup))
      (when (seq jobs)
        (try
          (doseq [{:keys [peer send! start count] job :id} jobs]
            (send-packet! pool peer send! {:op :run :id id :job job :uniforms values :start start :count count}))
          (let [chunks (collect jobs deadline)
                checked (when (and (< (System/nanoTime) deadline) (every? some? chunks))
                          (checked-slices pool group env jobs chunks))
                batch (when (and checked (every? second checked))
                        (unpack plan (:count group) (map first checked) (map second checked)))]
            (if (and batch (< (System/nanoTime) deadline))
              (do (swap! (:state pool) update :completed inc) batch)
              (do (swap! (:state pool) update :missed inc) nil)))
          (finally
            (locking (:lock pool)
              (doseq [{:keys [peer id]} jobs :when (= id (get-in @(:peers pool) [peer :job :id]))]
                ;; Keep at most this one physical job outstanding. Its eventual
                ;; completion frees the peer, without applying it to a later frame.
                (swap! (:peers pool) assoc-in [peer :job :expired?] true)))))))))

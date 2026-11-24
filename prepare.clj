(require '[afterglow.render.chain :as chain]
         '[afterglow.render.distributed :as distributed]
         '[afterglow.render.ir :as ir]
         '[clojure.data.json :as json]
         '[cognitect.transit :as transit])
(import '[java.io ByteArrayOutputStream])

(def positions (mapv (fn [i] [(/ (double i) 64) (/ (double (mod i 8)) 8) 0.0]) (range 64)))
(def uvs (mapv (fn [i] (when (even? i) [(/ (double (- 63 i)) 64) 0.125])) (range 64)))
(def targets (mapv #(keyword (str "head-" %)) (range 64)))
(defn literal [value] {:op :const :value value})

(defn stage [i]
  (let [parameter (keyword (str "level-" i))
        level {:op :param :key parameter}
        outputs (if (zero? i)
                  {:color (literal [0.0625 0.125 0.25]) :focus (literal 0.0625)}
                  {:color {:op :vec3 :args [level {:op :surface-uv :axis :u} {:op :position :axis :x}]}
                   :focus level})
        group (distributed/prepare-group outputs positions (ir/compile-batch outputs) uvs)]
    {:kind :batch :source {:instance-id i}
     :batch {:target-ids targets :blend (if (zero? i) :replace :max) :opacity (if (zero? i) 1.0 0.5)
             :field-request {:group group :env {:params {parameter (/ (double (+ i 2)) 32)}}}}}))

(defn wire [message]
  (let [out (ByteArrayOutputStream.)]
    (transit/write (transit/writer out :json) message)
    (.toString out "UTF-8")))

(defn expected [group env]
  (let [{:keys [count outputs]} (ir/evaluate-batch (:cpu-plan group) env (:positions group) (:surface-uvs group))
        layout (get-in group [:packet :plan :outputs])]
    (vec (for [row (range count), {:keys [attribute components]} layout, component (range components)]
           (aget ^doubles (get-in outputs [attribute :values]) (+ (* row components) component))))))

(defn run-data [fused job]
  (let [{:keys [group env]} (get-in fused [0 :batch :field-request])
        {:keys [id plan]} (:packet group)]
    {:wire (wire {:op :run :id id :job job :start 0 :count (:count group)
                  :uniforms (#'distributed/uniforms plan env)})
     :expected (expected group env)}))

(defn shader-case [n]
  (let [blocks (mapv stage (range (inc n)))
        compile (partial chain/fuse (chain/create-cache) distributed/prepare-group)
        fused (compile blocks)
        revised (compile (assoc-in blocks [n :batch :field-request :env :params (keyword (str "level-" n))] 0.96875))
        group-at #(get-in % [0 :batch :field-request :group])
        group (group-at fused)
        packet (:packet group)
        first-frame (run-data fused (str n "-first"))
        second-frame (run-data revised (str n "-revised"))]
    (assert (= 1 (count fused) (count revised)))
    (assert (identical? group (group-at revised)))
    (assert (not= (:expected first-frame) (:expected second-frame)))
    (assert (contains? (get-in packet [:plan :inputs]) :surface-uv))
    {:layers n :heads (:count group) :stride (get-in packet [:plan :stride])
     :uniforms (count (get-in packet [:plan :uniforms]))
     :shaderBytes (count (.getBytes ^String (get-in packet [:plan :source]) "UTF-8"))
     :prepare (wire packet) :run [first-frame second-frame]}))

(spit (first *command-line-args*) (json/write-str (mapv shader-case [10 18 24])))

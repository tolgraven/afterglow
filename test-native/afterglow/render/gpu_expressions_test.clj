(ns afterglow.render.gpu-expressions-test
  (:require [afterglow.render.frame :as frame]
            [afterglow.render.gpu.expressions :as gpu]
            [afterglow.render.ir :as ir]
            [clojure.test :refer [deftest is]]))

(defn- const-node [x] {:op :const :value x})

(defn- param [key type] {:op :param :key key :type type})

(defn- operation [op & nodes] {:op op :args (vec nodes)})

(def position {:op :vec3 :args (mapv #(hash-map :op :position :axis %) [:x :y :z])})

(def fields
  {:color (operation :add (operation :multiply position (param :gain :vec3)) (param :bias :number))
   :intensity (operation :abs (operation :sin {:op :beat :clock :absolute}))
   :aim (operation :multiply position (operation :add {:op :bar} (const-node 1.0)))
   :focus (operation :add {:op :phrase :clock :absolute} {:op :time})
   :pair (param :two :vec2) :rgba (param :four :vec4)})

(def env {:params {:gain [0.1 0.2 0.3] :bias 0.25 :two [-1 4] :four [0 1 0.3 0.8]}
          :beat 8.5 :elapsed-beats 3.75 :elapsed-ms 100
          :meter {:beats-per-bar 3 :bars-per-phrase 4}})

(defn- verify [expected actual]
  (is (= (:count expected) (:count actual)))
  (is (= (set (keys (:outputs expected))) (set (keys (:outputs actual)))))
  (doseq [[key {:keys [type components values]}] (:outputs expected)
          :let [field (get-in actual [:outputs key]) computed (:values field)]]
    (is (= [type components] ((juxt :type :components) field)) (str key))
    (is (= (alength ^doubles values) (alength ^doubles computed)))
    (dotimes [i (alength ^doubles values)]
      (let [a (aget ^doubles values i) b (aget ^doubles computed i)
            ;; Apple Software Renderer uses an approximate sin instruction.
            ;; Only the explicitly sinusoidal intensity field has this tolerance.
            absolute (if (= key :intensity) 0.001 0.000003)]
        (is (< (abs (- a b)) (+ absolute (* 0.000003 (abs a)))) (str key " at " i))))))

(deftest execute-a-multi-output-shader-against-the-independent-cpu-batch
  (let [positions (mapv (fn [i] [(/ i 39.0) (- (mod i 7) 3) (* -0.005 i i)]) (range 65))
        ordered (double-array (mapcat identity positions)) batch (ir/compile-batch fields)
        runner (gpu/open! fields ordered)]
    (try
      (let [first-result (gpu/evaluate! runner env)]
        (verify (ir/evaluate-batch batch env positions) first-result)
        (let [new-env (-> env (assoc :elapsed-ms 12 :beat 0.75) (assoc-in [:params :gain] [-1 0 1]))]
          (verify (ir/evaluate-batch batch new-env positions) (gpu/evaluate! runner new-env))
          (verify (ir/evaluate-batch batch env positions) first-result)))
      (doseq [bad [(dissoc env :elapsed-beats) (assoc-in env [:meter :beats-per-bar] 0)
                   (assoc-in env [:params :gain] [1 2]) (assoc-in env [:params :bias] ##Inf)]]
        (is (thrown? clojure.lang.ExceptionInfo (gpu/evaluate! runner bad))))
      (verify (ir/evaluate-batch batch env ordered) (gpu/evaluate! runner env))
      (finally (.close runner)))
    (is (thrown? clojure.lang.ExceptionInfo (gpu/evaluate! runner env)))))

(defn- beat-angle [op axis clock]
  (operation op (operation :add {:op :position :axis axis} {:op :beat :clock clock})))

(deftest periodic-native-geometry-keeps-beat-clocks-and-ordinary-fields-separate
  (let [private-key ::gpu/beat-phase-0
        absolute (beat-angle :cos :x :absolute)
        elapsed (beat-angle :sin :z :elapsed)
        fields {:aim (operation :vec3 absolute (const-node 1.0) elapsed)
                :direction (operation :vec3 (operation :floor absolute) (const-node 0.0) (const-node 1.0))
                :color (operation :vec3 (operation :fract {:op :beat :clock :absolute})
                                  (param private-key :number) (const-node 0.75))}
        positions [[0.55 3.5 -1.5] [-2.75 3.5 0.9]]
        capture {:beat 200000.75 :elapsed-beats 18.150000000000123 :params {private-key 0.25}}
        alternate (assoc capture :beat 18.125 :elapsed-beats 725000.375)
        group (gpu/group fields positions)
        values (zipmap (map (juxt :path #(contains? % :phase-position-ceiling)) (:bindings group))
                       (gpu/capture-inputs (:bindings group) capture))
        reference (ir/compile-batch fields)]
    (is (= [200000.75] (values [[:beat] false])))
    (is (= [0.25] (values [[:params private-key] false])))
    (is (< (abs (first (values [[:beat] true]))) Math/PI))
    (is (< (abs (first (values [[:elapsed-beats] true]))) Math/PI))
    (is (not= (values [[:beat] true]) (values [[:elapsed-beats] true])))
    (with-open [runner (gpu/open! fields positions)]
      (doseq [env [capture alternate]]
        (let [expected (ir/evaluate-batch reference env positions)
              actual (gpu/evaluate! runner env)]
          (verify expected actual)
          (doseq [field [:direction :color]]
            (is (= (vec (get-in expected [:outputs field :values]))
                   (vec (get-in actual [:outputs field :values])))))))
      (doseq [bad [(dissoc capture :elapsed-beats) (assoc capture :beat ##Inf)
                   (assoc capture :beat 1.0e18)]]
        (is (thrown? clojure.lang.ExceptionInfo (gpu/evaluate! runner bad)))))))

(def airie-aim-operands
  "Tolglow #609 capture at show time 9,075 ms (tolglow 2a5add3c,
  native-movement-555/aim-operands.json). Head 5 crossed a fine-pan step."
  {:aim (operation :vec3
                   (operation :add
                              (operation :multiply {:op :position :axis :x} (const-node -0.35))
                              (operation :multiply (param :width :number)
                                         (operation :sin (operation :add {:op :position :axis :x} {:op :beat}))))
                   (param :height :number) (const-node 0.9))
   :env {:params {:width 1.6562500000000462 :height 0.9261703921760138}
         :beat 18.150000000000123 :elapsed-beats 18.150000000000123 :time-ms 9075
         :meter {:beats-per-bar 4 :bars-per-phrase 4}}
   :positions (mapv #(vector % 3.5 -1.5)
                    [-3.85 -2.75 -1.65 -0.5499999999999998 0.5500000000000003
                     1.65 2.7500000000000004 3.850000000000001])
   :head-5-x -0.4392796365045701
   :unlowered-native-x -0.43928152322769165})

(deftest captured-airie-aim-phase-reaches-the-shader-reduced
  ;; The same tree under :color is an ordinary field and keeps float32 phase
  ;; addition; under :aim the captured elapsed beat is reduced in double first.
  (let [{:keys [aim env positions head-5-x unlowered-native-x]} airie-aim-operands
        fields {:aim aim :color aim}
        group (gpu/group fields positions)
        phases (keep (fn [[binding value]] (when (:phase-position-ceiling binding) [(:path binding) value]))
                     (map vector (:bindings group) (gpu/capture-inputs (:bindings group) env)))
        reference (ir/evaluate-batch (ir/compile-batch fields) env positions)
        x-errors (fn [result field]
                   (let [^doubles expected (get-in reference [:outputs :aim :values])
                         ^doubles values (get-in result [:outputs field :values])]
                     (mapv #(abs (- (aget values (* 3 %)) (aget expected (* 3 %)))) (range (count positions)))))]
    (is (= head-5-x (aget ^doubles (get-in reference [:outputs :aim :values]) 12)))
    (is (= 1 (count phases)) "Only the elapsed clock reaches the shader as a phase")
    (let [[path [phase]] (first phases)]
      (is (= [:elapsed-beats] path))
      (is (<= (abs (- phase (- (:elapsed-beats env) (* 6 Math/PI)))) (Math/ulp (float 1.0)))))
    (with-open [runner (gpu/open! fields positions)]
      (let [actual (gpu/evaluate! runner env)
            renderer (str (get-in runner [:resources :renderer]))
            apple? (boolean (re-find #"^Apple M\d" renderer))
            lowered (x-errors actual :aim)
            ordinary (x-errors actual :color)]
        (verify (update reference :outputs dissoc :color) (update actual :outputs dissoc :color))
        (println "Airie aim phase" {:renderer renderer :max-lowered-x-error (apply max lowered)
                                    :max-ordinary-x-error (apply max ordinary)
                                    :head-5-ordinary-x (aget ^doubles (get-in actual [:outputs :color :values]) 12)})
        (when apple?
          ;; Measured bounds on Apple M-series; other drivers report only.
          (is (= unlowered-native-x (aget ^doubles (get-in actual [:outputs :color :values]) 12))
              "The ordinary field reproduces the captured Airie native value")
          (is (< (apply max lowered) 4.0e-7))
          (is (< (nth lowered 4) (/ (nth ordinary 4) 4))))))))

(deftest zero-size-and-nonfinite-results
  (with-open [runner (gpu/open! fields [])]
    (verify (ir/evaluate-batch (ir/compile-batch fields) env []) (gpu/evaluate! runner env)))
  (let [outputs {:focus (operation :sqrt (param :value :number))}]
    (with-open [runner (gpu/open! outputs [[0 0 0]])]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"nonfinite" (gpu/evaluate! runner {:params {:value -1}})))
      (is (= [2.0] (vec (get-in (gpu/evaluate! runner {:params {:value 4}}) [:outputs :focus :values]))))))
  (is (thrown? clojure.lang.ExceptionInfo (gpu/open! fields [[1 2]])))
  (is (thrown? clojure.lang.ExceptionInfo (gpu/open! fields (double-array [1 2 3 4])))))

(deftest shader-fields-pack-through-the-existing-multi-universe-output-path
  (let [ids (vec (range 256))
        fixtures (mapv (fn [id]
                         (let [base (+ 510 (* 4 id))]
                           {:id id :universe (+ 4 (quot base 512)) :address (inc (mod base 512))
                            :channels {:red 1 :green 2 :blue 3 :focus 4}})) ids)
        positions (mapv #(vector (/ (mod % 16) 16.0) 0.5 0.75) ids)
        outputs {:color position :focus {:op :beat :clock :absolute}}
        clock {:beat 0.25}
        patch (frame/compile-patch fixtures)
        pack (fn [batch] (update-vals (:universes (frame/resolve-batches patch [(assoc batch :target-ids ids)]))
                                      vec))]
    (with-open [runner (gpu/open! outputs positions)]
      (let [actual (pack (gpu/evaluate! runner clock))
            expected (pack (ir/evaluate-batch (ir/compile-batch outputs) clock positions))]
        (is (= #{4 5 6} (set (keys actual))))
        (is (= expected actual))
        (is (some pos? (map #(bit-and 255 %) (mapcat identity (vals actual)))))))))

(deftest independent-surface-uvs-share-the-world-position-buffer-only-when-required
  (let [positions [[1.0 2.0 0.3] [1.0 2.0 0.3] [2.0 1.0 0.5]]
        uvs [[0.75 0.4] [-0.5 1.5] nil]
        fields {:focus (operation :add {:op :position :axis :z} {:op :surface-uv :axis :u})
                :pair (operation :vec2 {:op :surface-uv :axis :v} {:op :position :axis :x})}
        plan (ir/compile-batch fields)]
    (doseq [chart [nil uvs]]
      (with-open [runner (gpu/open! fields positions {:surface-uvs chart})]
        (verify (ir/evaluate-batch plan {} positions chart) (gpu/evaluate! runner {}))))
    (is (not= (gpu/group fields positions uvs)
              (gpu/group fields positions (assoc-in uvs [1 0] 0.85))))
    (is (= (gpu/group {:aim position} positions) (gpu/group {:aim position} positions uvs)))))

(deftest uniform-groups-read-one-native-vertex-and-return-owned-field-arrays
  (let [positions (mapv (fn [i] [i (* -0.2 i) (* 0.5 i)]) (range 13))
        outputs {:color (param :gain :vec3) :white (param :bias :number)}
        plan (ir/compile-batch outputs)]
    (with-open [runner (gpu/open! outputs positions)]
      (let [{:keys [count vertices readback]} (:resources runner)
            first-frame (gpu/evaluate! runner env)
            second-env (assoc-in env [:params :bias] 0.8)]
        (is (= [13 1 4] [count vertices (.capacity ^java.nio.FloatBuffer readback)]))
        (verify (ir/evaluate-batch plan env positions) first-frame)
        (aset-double ^doubles (get-in first-frame [:outputs :color :values]) 0 99.0)
        (verify (ir/evaluate-batch plan second-env positions) (gpu/evaluate! runner second-env))))
    (doseq [varying [position {:op :surface-uv :axis :u}]]
      (with-open [runner (gpu/open! (assoc outputs :extra varying) positions)]
        (is (= (count positions) (get-in runner [:resources :vertices])))))
    (with-open [empty-runner (gpu/open! outputs [])]
      (is (zero? (get-in empty-runner [:resources :vertices])))
      (is (zero? (:count (gpu/evaluate! empty-runner env)))))))

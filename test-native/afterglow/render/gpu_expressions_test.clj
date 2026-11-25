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

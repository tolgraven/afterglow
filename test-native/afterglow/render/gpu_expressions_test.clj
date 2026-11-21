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
      (let [a (aget ^doubles values i) b (aget ^doubles computed i)]
        (is (< (abs (- a b)) (+ 0.0002 (* 0.000003 (abs a)))) (str key " at " i))))))

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

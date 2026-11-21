(ns afterglow.render.ir-test
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.string :as str]
            [afterglow.render.ir :as ir]))

(defn- c [value] {:op :const :value value})
(defn- near? [a b] (< (Math/abs (double (- a b))) 1.0e-9))

(deftest explicit-inputs-and-reusable-compiled-functions
  (let [expression {:op :add :args [{:op :param :key :level}
                                    {:op :multiply :args [{:op :position :axis :x}
                                                         {:op :time}]}]}
        f (ir/compile-expression expression)
        env {:params {:level 2.0} :position [3.0 4.0 5.0] :elapsed-ms 4.0}]
    (is (= 14.0 (f env)))
    (is (= 17.0 (f (assoc env :elapsed-ms 5.0))))
    (is (= 14.0 (f env)))
    (is (= env {:params {:level 2.0} :position [3.0 4.0 5.0] :elapsed-ms 4.0}))
    (is (= 50 (ir/evaluate {:op :time :clock :absolute} {:time-ms 50})))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Missing expression parameter"
                          (f (assoc env :params {}))))))

(deftest vector-arithmetic-and-curves
  (is (= [0.25 0.5 0.75]
         (ir/evaluate {:op :multiply :args [(c [0.5 1.0 1.5]) (c 0.5)]} {})))
  (is (= [1.0 0.0 0.25]
         (ir/evaluate {:op :clamp :args [(c [2.0 -1.0 0.25]) (c 0.0) (c 1.0)]} {})))
  (is (= [0.25 0.25 0.75]
         (ir/evaluate {:op :mix :args [(c [0.0 0.0 1.0]) (c [1.0 1.0 0.0]) (c 0.25)]} {})))
  (is (= [1 2 3] (ir/evaluate {:op :vec3 :args [(c 1) (c 2) (c 3)]} {})))
  (is (near? 1.0 (ir/evaluate {:op :sin :args [(c (/ Math/PI 2))]} {})))
  (is (= 0.75 (ir/evaluate {:op :fract :args [(c -0.25)]} {})))
  (is (= [0.5 1.0] (ir/evaluate {:op :sqrt :args [(c [0.25 1.0])]} {}))))

(deftest rejects-invalid-schemas-and-numerical-domains
  (doseq [bad [{:op :unknown}
               {:op :const :value Double/NaN}
               {:op :const :value [1]}
               {:op :position :axis :q}
               {:op :time :clock :wall}
               {:op :param :key "level"}
               {:op :add :args []}
               {:op :divide :args [(c 1)]}
               {:op :add :args [(c [1 2]) (c [1 2 3])]}
               {:op :vec3 :args [(c [1 2 3]) (c 2) (c 3)]}
               {:op :mix :args [(c [1 2]) (c [3 4]) (c [0.5 0.5])]}
               {:op :add :args [{:op :param :key :a :type :vec3}
                               {:op :param :key :a}]}]]
    (is (seq (ir/validate-expression bad)) (pr-str bad)))
  (doseq [bad [{:op :divide :args [(c 1) (c 0)]}
               {:op :sqrt :args [(c -1)]}
               {:op :pow :args [(c -2) (c 2)]}
               {:op :clamp :args [(c 2) (c 10) (c 0)]}
               {:op :multiply :args [(c Double/MAX_VALUE) (c 2)]}]]
    (is (thrown? clojure.lang.ExceptionInfo (ir/evaluate bad {}))))
  (is (thrown? clojure.lang.ExceptionInfo
               (ir/evaluate {:op :param :key :position :type :vec3}
                            {:params {:position [1 2]}}))))

(deftest bounded-nesting
  (let [deep (nth (iterate #(hash-map :op :abs :args [%]) (c 1)) 66)]
    (is (seq (ir/validate-expression deep)))))

(deftest generated-shader-has-typed-bindings-and-safe-uniforms
  (let [expression {:op :multiply
                    :args [{:op :param :key :color :type :vec3}
                           {:op :param :key :gain}
                           {:op :sin :args [{:op :time}]}]}
        generated (ir/emit-glsl expression)]
    (is (= :vec3 (:type generated)))
    (is (= {:color {:name "u_param_0" :type :vec3}
            :gain {:name "u_param_1" :type :number}} (:uniforms generated)))
    (is (str/starts-with? (:source generated) "#version 300 es"))
    (is (str/includes? (:source generated) "uniform vec3 u_param_0;"))
    (is (str/includes? (:expression generated) "vec3(u_param_1)"))
    (is (not (str/includes? (:source generated) "{{")))
    (is (= generated (ir/emit-glsl expression)))
    (is (= :vec3 (ir/expression-type expression)))
    (is (thrown? clojure.lang.ExceptionInfo (ir/emit-glsl (c Double/MAX_VALUE))))))

(deftest batch-keeps-aim-color-and-focus-in-distinct-owned-fields
  (let [expressions {:color {:op :multiply :args [(c [1.0 0.5 0.25]) {:op :param :key :level}]}
                     :aim {:op :vec3 :args [{:op :position :axis :x} (c 2.0) {:op :time}]}
                     :focus {:op :add :args [{:op :position :axis :z} (c 0.25)]}}
        plan (ir/compile-batch expressions)
        env {:params {:level 0.5} :elapsed-ms 4.0}
        positions [[0.0 0.0 0.0] [1.0 2.0 0.5]]
        result (ir/evaluate-batch plan env positions)
        flat-result (ir/evaluate-batch plan env (double-array (mapcat identity positions)))]
    (is (= 2 (:count result)))
    (doseq [[attribute expression] expressions]
      (let [field (get-in result [:outputs attribute])
            expected (mapcat (fn [position]
                               (let [value (ir/evaluate expression (assoc env :position position))]
                                 (if (vector? value) value [value]))) positions)]
        (is (= (vec expected) (vec (:values field))))
        (is (= (vec (:values field)) (vec (get-in flat-result [:outputs attribute :values]))))))
    (is (= 3 (get-in result [:outputs :aim :components])))
    (is (= 1 (get-in result [:outputs :focus :components])))
    (aset-double ^doubles (get-in result [:outputs :focus :values]) 0 0.9)
    (is (= [0.25 0.75] (vec (get-in flat-result [:outputs :focus :values]))))
    (is (= [0.0 2.0 4.0 1.0 2.0 4.0] (vec (get-in result [:outputs :aim :values]))))
    (is (= positions [[0.0 0.0 0.0] [1.0 2.0 0.5]]))))

(deftest batch-rejects-invalid-shapes-and-nonfinite-positions
  (let [plan (ir/compile-batch {:focus (c 0.5)})]
    (is (thrown? clojure.lang.ExceptionInfo (ir/compile-batch {})))
    (is (thrown? clojure.lang.ExceptionInfo (ir/evaluate-batch plan {} (double-array [1 2]))))
    (is (thrown? clojure.lang.ExceptionInfo (ir/evaluate-batch plan {} [[0 0 Double/NaN]])))
    (is (= 0 (:count (ir/evaluate-batch plan {} []))))))

(deftest musical-transport-is-explicit-continuous-and-meter-aware
  (let [env {:beat 18.0 :elapsed-beats 6.0 :meter {:beats-per-bar 3 :bars-per-phrase 4}}]
    (doseq [[op elapsed absolute] [[:beat 6.0 18.0] [:bar 2.0 6.0] [:phrase 0.5 1.5]]]
      (is (= elapsed (ir/evaluate {:op op} env)))
      (is (= absolute (ir/evaluate {:op op :clock :absolute} env)))
      (is (= :number (ir/expression-type {:op op})))
      (is (seq (ir/validate-expression {:op op :clock :wall}))))
    (is (= 0.75 (ir/evaluate {:op :bar} (assoc env :elapsed-beats 2.25))))
    (is (= 0.25 (ir/evaluate {:op :phrase} (assoc env :meter {:beats-per-bar 6 :bars-per-phrase 4}))))
    (doseq [bad [(dissoc env :elapsed-beats) (assoc env :elapsed-beats Double/NaN)
                 (assoc env :meter {}) (assoc-in env [:meter :beats-per-bar] 0)
                 (assoc-in env [:meter :bars-per-phrase] -1)]]
      (is (thrown? clojure.lang.ExceptionInfo (ir/evaluate {:op :phrase} bad))))
    (let [expression {:op :add :args [{:op :phrase} {:op :beat :clock :absolute}]}
          shader (ir/emit-glsl expression)
          batch (ir/evaluate-batch (ir/compile-batch {:focus expression}) env [[0 0 0] [1 0 0]])]
      (is (= [18.5 18.5] (vec (get-in batch [:outputs :focus :values]))))
      (is (= "u_elapsed_beats" (get-in shader [:inputs :elapsed-beats])))
      (is (= "u_beat" (get-in shader [:inputs :beat])))
      (is (= "u_beats_per_bar" (get-in shader [:inputs :beats-per-bar])))
      (is (= "u_bars_per_phrase" (get-in shader [:inputs :bars-per-phrase])))
      (is (str/includes? (:source shader) "uniform float u_bars_per_phrase;")))))

(deftest compiled-batch-components-match-scalar-oracle-across-operators
  (let [position {:op :position :axis :x}
        expressions {:sum {:op :add :args [position (c 0.25) (c [0.2 0.4 0.6])]}
                     :difference {:op :subtract :args [(c [0.2 0.4]) position]}
                     :negative {:op :subtract :args [position]}
                     :product {:op :multiply :args [(c [0.2 0.3 0.4 0.5]) position (c 2)]}
                     :quotient {:op :divide :args [position (c 2)]}
                     :minimum {:op :min :args [position (c 0.1) (c 0.3)]}
                     :maximum {:op :max :args [position (c 0.1) (c 0.3)]}
                     :sine {:op :sin :args [position]} :cosine {:op :cos :args [position]}
                     :absolute {:op :abs :args [position]} :floor {:op :floor :args [position]}
                     :fraction {:op :fract :args [position]} :root {:op :sqrt :args [position]}
                     :power {:op :pow :args [position (c 2.5)]}
                     :clamp {:op :clamp :args [position (c 0.1) (c 0.3)]}
                     :mix {:op :mix :args [(c [0.1 0.2 0.3]) (c [0.8 0.7 0.6]) position]}
                     :vector {:op :vec3 :args [position {:op :param :key :gain} {:op :time}]}}
        env {:params {:gain 0.75} :elapsed-ms 1.25}
        positions [[0.2 0 0] [0.7 0 0] [1.2 0 0]]
        result (ir/evaluate-batch (ir/compile-batch expressions) env positions)]
    (doseq [[attribute expression] expressions]
      (let [expected (mapcat (fn [p] (let [value (ir/evaluate expression (assoc env :position p))]
                                      (if (vector? value) value [value]))) positions)]
        (is (every? true? (map near? expected (get-in result [:outputs attribute :values]))) (str attribute))))
    (doseq [expression [{:op :divide :args [position (c 0)]}
                        {:op :sqrt :args [{:op :subtract :args [position]}]}
                        {:op :pow :args [(c -2) position]}
                        {:op :clamp :args [position (c 2) (c 1)]}]]
      (is (thrown? clojure.lang.ExceptionInfo
                   (ir/evaluate-batch (ir/compile-batch {:value expression}) env positions))))))

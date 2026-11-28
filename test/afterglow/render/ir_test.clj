(ns afterglow.render.ir-test
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [afterglow.render.ir :as ir]
            [afterglow.render.ir-corpus :as corpus]
            [afterglow.render.ir-reference :as reference]))

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

(deftest partial-maximum-blend-uses-the-same-arithmetic-for-scalar-and-packed-results
  (doseq [[prior incoming] [[(c 0.75) (c 0.25)]
                            [(c [0.75 0.25]) (c 0.5)]
                            [(c 0.5) (c [0.75 0.25 0.5])]
                            [(c [0.75 0.25 0.5 0.5]) (c [0.25 0.75 0.5 0.5])]]
          amount [0.0 0.25 1.0]]
    (let [fraction (c amount)
          expression (ir/partial-max-blend prior incoming fraction)
          delta {:op :subtract :args [{:op :max :args [prior incoming]} prior]}
          reference {:op :add :args [prior {:op :multiply :args [fraction delta]}]}
          result (ir/evaluate reference {})
          expected (if (vector? result) result [result])
          outputs {:test expression}
          shader (ir/emit-glsl-batch outputs)
          values (get-in (ir/evaluate-batch (ir/compile-batch outputs) {} [[0 0 0] [1 1 1]])
                         [:outputs :test :values])]
      (is (= result (ir/evaluate expression {})))
      (is (= (into expected expected) (vec values)))
      (is (empty? (:inputs shader)))
      (is (= (count expected) (:stride shader)))
      (is (str/includes? (:source shader) "return prior + amount * (max(prior, incoming) - prior);"))
      (is (str/includes? (:source (ir/emit-glsl expression)) "afterglow_max_blend("))
      (is (seq (ir/validate-expression (into {} expression))))
      (is (not (str/includes? (:source (ir/emit-glsl-batch {:test reference})) "afterglow_max_blend"))))))

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

(deftest vertex-shader-packs-named-fields-in-deterministic-order
  (let [outputs {:motion/focus {:op :multiply :args [{:op :param :key :gain} {:op :phrase}]}
                 :aim {:op :vec2 :args [{:op :position :axis :x} {:op :time :clock :absolute}]}
                 :color {:op :multiply :args [{:op :param :key :palette/red :type :vec3}
                                             {:op :param :key :gain}]}}
        {:keys [stride source inputs uniforms] fields :outputs :as shader} (ir/emit-glsl-batch outputs)
        plan (ir/compile-batch outputs)]
    (is (= [[:aim :vec2 2 0 "out_0"] [:color :vec3 3 2 "out_1"] [:motion/focus :number 1 5 "out_2"]]
           (mapv (juxt :attribute :type :components :offset :varying) fields)))
    (is (= 6 stride))
    (is (= (mapv :attribute fields) (mapv :attribute (:outputs plan))))
    (is (= {:time-ms "u_time_ms" :position "v_position" :elapsed-beats "u_elapsed_beats"
            :beats-per-bar "u_beats_per_bar" :bars-per-phrase "u_bars_per_phrase"} inputs))
    (is (= {:gain {:name "u_param_0" :type :number} :palette/red {:name "u_param_1" :type :vec3}} uniforms))
    (is (str/includes? source "layout(location = 0) in vec3 v_position"))
    (is (str/includes? source "out vec3 out_1;"))
    (is (not (re-find #"\{\{|palette/red|u_elapsed_ms" source)))
    (is (= shader (ir/emit-glsl-batch (into (array-map) (reverse (seq outputs))))))
    (is (empty? (:inputs (ir/emit-glsl-batch {:level (c 0.5)}))))))

(deftest vertex-shader-rejects-invalid-batches-before-linking
  (doseq [outputs [{} {"x" (c 0)} {:color (c [0 Double/MAX_VALUE 0])}
                   {:a {:op :param :key :p :type :vec2} :b {:op :param :key :p}}
                   (into {} (map (fn [i] [(keyword (str "field" i)) (c i)]) (range 65)))]]
    (is (thrown? clojure.lang.ExceptionInfo (ir/emit-glsl-batch outputs)))))

(deftest spatial-batch-samples-this-frames-clock-and-parameters
  (let [position {:op :position :axis :z}
        expression {:op :add :args [position {:op :param :key :rgb :type :vec3}
                                    {:op :phrase} {:op :time :clock :absolute}]}
        plan (ir/compile-batch {:color expression})
        positions [[3 2 1] [-1 0 5]]
        run (fn [env points] (vec (get-in (ir/evaluate-batch plan env points) [:outputs :color :values])))
        first-frame {:params {:rgb [1 4 7]} :time-ms 4 :elapsed-beats 24 :meter {:beats-per-bar 3 :bars-per-phrase 4}}
        second-frame {:params {:rgb [2 5 8]} :time-ms 8 :elapsed-beats 10 :meter {:beats-per-bar 5 :bars-per-phrase 2}}]
    (doseq [env [first-frame second-frame first-frame]]
      (let [expected (vec (mapcat #(ir/evaluate expression (assoc env :position %)) positions))]
        (is (= (mapv double expected) (run env positions)))
        (is (= (mapv double expected) (run env (double-array (mapcat identity positions)))))))
    (is (thrown? clojure.lang.ExceptionInfo (run (dissoc second-frame :meter) positions)))))

(deftest batch-binary-arithmetic-preserves-broadcasts-and-fault-locations
  (let [x {:op :position :axis :x}
        positions [[-4.0 1.0 2.0] [0.25 3.0 4.0]]
        evaluate (fn [expression] (ir/evaluate-batch (ir/compile-batch {:field expression}) {} positions))]
    (doseq [op [:add :multiply :min :max]
            args [[x] [x (c [0.5 -2.0 4.0])] [(c [0.5 -2.0 4.0]) x]
                  [(c 0.25) x (c -2.0) (c 4.0)]]]
      (let [expression {:op op :args args}
            scalar (ir/compile-expression expression)
            expected (double-array (mapcat (fn [point] (let [value (scalar {:position point})]
                                                        (if (vector? value) value [value]))) positions))]
        (is (java.util.Arrays/equals expected ^doubles (get-in (evaluate expression) [:outputs :field :values]))
            (str op " " args))))
    ;; Both operands can fail. The first failing child must still identify its
    ;; original expression path, even when the enclosing operation could mask it.
    (let [bad-rhs {:op :divide :args [x (c 0)]}
          bad-lhs {:op :multiply :args [(c Double/MAX_VALUE) x]}]
      (doseq [op [:add :multiply :min :max]
              [args path] [[[bad-lhs bad-rhs] [:args 0]] [[x bad-rhs] [:args 1]]]]
        (try
          (evaluate {:op op :args args})
          (is false (str "Expected an arithmetic fault for " op))
          (catch clojure.lang.ExceptionInfo error
            (is (= path (:path (ex-data error))))))))))

;; tolgraven/tolglow#872: shared subexpressions and frame-constant work run once
;; per call. ir-reference is the unshared evaluator these must match bit for bit.

(defn- outcome
  "Result or fault of one evaluation, comparable with ="
  [evaluate]
  (try (let [{:keys [count outputs]} (evaluate)]
         {:count count
          :outputs (into {} (map (fn [[k f]] [k (assoc f :values (mapv #(Double/doubleToRawLongBits %) (:values f)))]))
                         outputs)})
       (catch clojure.lang.ExceptionInfo error
         {:fault (ex-message error) :data (ex-data error)})))

(defn- agree [outputs env positions & [uvs]]
  (let [shared (outcome #(ir/evaluate-batch (ir/compile-batch outputs) env positions uvs))]
    (is (= (outcome #(reference/evaluate-batch (reference/compile-batch outputs) env positions uvs)) shared)
        (pr-str (keys outputs)))
    shared))

(deftest shared-evaluation-is-bit-identical-to-the-unshared-evaluator
  (let [positions (corpus/matrix 300 30)
        flat (double-array (mapcat identity positions))]
    (doseq [{:keys [id outputs]} (corpus/families 10)
            beat [0.0 33.75 -7.125]]
      (testing id
        (let [env (assoc corpus/environment :beat beat :elapsed-beats (* 0.5 beat) :elapsed-ms (* 500.0 beat))
              result (agree outputs env positions)]
          (is (nil? (:fault result)))
          (is (= result (agree outputs env flat)))
          (agree outputs env [])
          (agree outputs env (subvec positions 7 8)))))))

(deftest shared-terms-run-once-per-head-and-frame-constant-terms-once-per-call
  (let [{:keys [outputs]} (first (filter #(= :soft-sphere (:id %)) (corpus/families 10)))
        plan (ir/compile-batch outputs)
        [color] (:outputs plan)]
    ;; The tree visits 321 nodes per head; only the head's distance, the edge
    ;; and two scaled components differ by head.
    (is (= 14 (count (:per-head plan))))
    (is (<= 10 (count (:hoisted plan))))
    (is (= [0 1] (:per-head color)) "the constant blue component is filled once")
    (is (:spatial? color)))
  (let [x {:op :position :axis :x}
        shared {:op :sin :args [{:op :multiply :args [x {:op :param :key :k}]}]}
        constant {:op :cos :args [{:op :multiply :args [{:op :time} (corpus/c 0.25)]}]}
        outputs {:color {:op :vec3 :args [shared {:op :multiply :args [shared constant]} constant]}
                 :white {:op :add :args [shared constant]}
                 :dimmer constant}
        plan (ir/compile-batch outputs)]
    (testing "a term shared across components and fields is one instruction"
      (is (= 4 (count (:per-head plan))) "multiply, sin, the colour product and the white sum")
      (is (= [0 1] (:per-head (first (:outputs plan))))))
    (testing "a frame-constant subtree inside a spatial field is not evaluated per head"
      (is (empty? (:hoisted plan)) "the dimmer field already computed it")
      (is (= 3 (count (:constant-fields plan)))))
    (agree outputs {:params {:k 0.3} :elapsed-ms 12.5} (corpus/matrix 40 8))
    (let [hoisted (ir/compile-batch (dissoc outputs :dimmer))]
      (is (= 3 (count (:hoisted hoisted))))
      (agree (dissoc outputs :dimmer) {:params {:k 0.3} :elapsed-ms 12.5} (corpus/matrix 40 8)))))

(deftest shared-and-hoisted-faults-keep-their-message-data-and-order
  (let [x {:op :position :axis :x}
        z {:op :position :axis :z}
        c corpus/c
        ;; Fails at the head with x = 3, from whichever field reaches it first.
        bad-shared {:op :divide :args [(c 1.0) {:op :subtract :args [x (c 3.0)]}]}
        ;; Fails for every head and does not read a coordinate.
        bad-constant {:op :divide :args [(c 1.0) {:op :subtract :args [{:op :param :key :k} (c 0.5)]}]}
        ;; Fails at the first head only.
        bad-first {:op :sqrt :args [{:op :subtract :args [x (c 0.5)]}]}
        env {:params {:k 0.5}}
        positions (corpus/matrix 10 10)]
    (doseq [outputs [{:a {:op :add :args [bad-shared z]} :b {:op :multiply :args [z bad-shared]}}
                     {:color {:op :vec3 :args [z {:op :add :args [z bad-shared]} bad-shared]}}
                     {:a {:op :add :args [x bad-constant]}}
                     {:a {:op :add :args [bad-first bad-constant]}}
                     {:a {:op :add :args [x bad-first]} :b {:op :add :args [z bad-constant]}}
                     {:a {:op :add :args [z bad-constant]} :b {:op :add :args [x bad-first]}}
                     {:a bad-constant :b {:op :add :args [x bad-constant]}}
                     {:a {:op :vec2 :args [x bad-constant]}}]]
      (let [result (agree outputs env positions)]
        (is (#{"Division by zero" "Expression produced a non-finite value"} (:fault result)) (pr-str outputs)))
      (agree outputs env (assoc positions 0 [0.0 Double/NaN 0.0]))
      (agree outputs env (assoc positions 2 [0.0 Double/NaN 0.0]))
      (testing "no head, no evaluation"
        (is (= 0 (:count (agree outputs env []))))))
    (testing "an invalid first position still wins over a hoisted frame-constant fault"
      (is (= "Position must contain three finite coordinates"
             (:fault (agree {:a {:op :add :args [x bad-constant]}} env (assoc positions 0 [0.0 Double/NaN 0.0])))))
      (is (= "Division by zero" (:fault (agree {:a {:op :add :args [x bad-constant]}} env positions)))))
    (let [{:keys [fault data]} (agree {:a {:op :add :args [bad-shared z]} :b {:op :multiply :args [z bad-shared]}}
                                      env positions)]
      (is (= "Division by zero" fault))
      (is (= {:type ::ir/invalid-expression :path [:args 0] :message "Division by zero"} data)
          "the first occurrence in evaluation order reports the fault"))))

(deftest signed-zero-constants-stay-apart
  (let [x {:op :position :axis :x}
        result (agree {:negative {:op :multiply :args [x (corpus/c -0.0)]}
                       :positive {:op :multiply :args [x (corpus/c 0.0)]}}
                      {} [[1.0 0.0 0.0] [2.5 0.0 0.0]])
        bits (fn [k] (get-in result [:outputs k :values]))]
    (is (= (repeat 2 (Double/doubleToRawLongBits -0.0)) (bits :negative)))
    (is (= (repeat 2 (Double/doubleToRawLongBits 0.0)) (bits :positive)))))

(deftest every-operator-and-clock-agrees-without-faults
  (let [x {:op :position :axis :x}
        z {:op :position :axis :z}
        c corpus/c
        wave {:op :sin :args [{:op :add :args [x {:op :beat :clock :absolute}]}]}
        outputs {:quad {:op :vec4 :args [{:op :floor :args [{:op :multiply :args [x (c 2.5)]}]}
                                         {:op :exp :args [wave]}
                                         {:op :pow :args [{:op :add :args [{:op :abs :args [wave]} (c 0.5)]} (c 1.5)]}
                                         {:op :min :args [wave z {:op :phrase} {:op :phrase :clock :absolute}]}]}
                 :pair {:op :vec2 :args [{:op :max :args [wave {:op :bar :clock :absolute}]}
                                         {:op :add :args [{:op :time :clock :absolute} {:op :time} wave]}]}
                 :level {:op :clamp :args [{:op :mix :args [wave {:op :fract :args [z]} (c 0.25)]} (c 0.0) (c 1.0)]}}
        result (agree outputs corpus/environment (corpus/matrix 60 10))]
    (is (nil? (:fault result)))
    (is (= [4 2 1] (map #(get-in result [:outputs % :components]) [:quad :pair :level])))))

(def ^:private fuzz-constants [0.0 -0.0 1.0 0.5 -2.0 3.0 1e300 -1e-300 0.1 7.0])

(def ^:private fuzz-leaves
  [{:op :position :axis :x} {:op :position :axis :y} {:op :position :axis :z}
   {:op :beat} {:op :bar} {:op :phrase} {:op :beat :clock :absolute} {:op :bar :clock :absolute}
   {:op :phrase :clock :absolute} {:op :time} {:op :time :clock :absolute}
   {:op :param :key :k} {:op :param :key :j}])

(defn- fuzz-batch
  "One random batch of 1–4 fields. Subtrees are reused by value across fields
  and components, as the authoring DSL does."
  [^java.util.Random rng]
  (let [pool (volatile! [])
        pick (fn [xs] (nth xs (.nextInt rng (count xs))))
        chance (fn [p] (< (.nextDouble rng) p))
        scalar (fn scalar [depth]
                 (cond
                   (and (seq @pool) (chance 0.3)) (pick @pool)
                   (or (zero? depth) (chance 0.2))
                   (if (chance 0.4) {:op :const :value (pick fuzz-constants)} (pick fuzz-leaves))
                   :else
                   (let [s #(scalar (dec depth))
                         op (pick [:add :subtract :multiply :divide :min :max :sin :cos :abs :floor :fract
                                   :exp :sqrt :pow :clamp :mix :add3 :min4 :max3 :negate])
                         e (case op
                             (:sin :cos :abs :floor :fract :exp :sqrt) {:op op :args [(s)]}
                             :negate {:op :subtract :args [(s)]}
                             (:add :subtract :multiply :divide :min :max :pow) {:op op :args [(s) (s)]}
                             :add3 {:op :add :args [(s) (s) (s)]}
                             :min4 {:op :min :args [(s) (s) (s) (s)]}
                             :max3 {:op :max :args [(s) (s) (s)]}
                             (:clamp :mix) {:op op :args [(s) (s) (s)]})]
                     (vswap! pool conj e)
                     e)))
        vector3 (fn vector3 [depth]
                  (case (.nextInt rng (if (pos? depth) 5 2))
                    0 {:op :vec3 :args [(scalar depth) (scalar depth) (scalar depth)]}
                    1 {:op :param :key :tint :type :vec3}
                    2 {:op :mix :args [(vector3 (dec depth)) {:op :const :value [0.0 -0.0 1.0]} (scalar depth)]}
                    3 (ir/partial-max-blend (vector3 (dec depth))
                                            {:op :multiply :args [(vector3 (dec depth)) (scalar depth)]} (scalar depth))
                    4 {:op :clamp :args [{:op :add :args [(vector3 (dec depth)) (scalar depth)]}
                                         {:op :const :value 0.0} {:op :const :value 1.0}]}))
        field (fn []
                (case (.nextInt rng 5)
                  (0 1) (scalar 5)
                  2 (vector3 3)
                  3 {:op :vec2 :args [(scalar 4) (scalar 4)]}
                  4 {:op :vec4 :args [(scalar 4) (scalar 3) (scalar 3) (scalar 4)]}))]
    (into {} (for [k (take (inc (.nextInt rng 4)) [:a :b :color :white])] [k (field)]))))

(deftest seeded-random-batches-agree-with-the-unshared-evaluator
  ;; After the external 6,000-batch probe in the tolgraven/afterglow#171 review.
  (let [rng (java.util.Random. 872875)
        env {:params {:k 0.5 :j -0.0 :tint [0.9 -0.0 0.25]}
             :beat 33.75 :elapsed-beats 1.625 :elapsed-ms 812.5 :time-ms 16875.0
             :meter {:beats-per-bar 4 :bars-per-phrase 4}}
        positions (mapv (fn [i] [(- (double (mod i 7)) 3.0) (* 0.5 (double (mod i 3))) (- (double (quot i 7)) 1.0)])
                        (range 21))
        flat (double-array (mapcat identity positions))
        tally (frequencies
               (for [_ (range 400)
                     :let [outputs (fuzz-batch rng)
                           env (if (< (.nextDouble rng) 0.5) env (assoc env :beat (- (.nextDouble rng) 0.5)))
                           points (if (< (.nextDouble rng) 0.5) positions flat)]]
                 (let [shared (outcome #(ir/evaluate-batch (ir/compile-batch outputs) env points))
                       unshared (outcome #(reference/evaluate-batch (reference/compile-batch outputs) env points))]
                   (cond (not= shared unshared) (do (is (= unshared shared) (pr-str outputs)) :mismatch)
                         (:fault shared) :fault
                         :else :value))))]
    (is (zero? (:mismatch tally 0)))
    (is (< 100 (:value tally 0)) (pr-str tally))
    (is (< 100 (:fault tally 0)) (pr-str tally))))

(deftest charted-fields-share-terms-like-world-fields
  (let [u {:op :surface-uv :axis :u}
        v {:op :surface-uv :axis :v}
        x {:op :position :axis :x}
        ring {:op :sin :args [{:op :add :args [{:op :multiply :args [u (corpus/c 6.0)]} {:op :beat}]}]}
        outputs {:color {:op :vec3 :args [ring {:op :multiply :args [ring v]} {:op :multiply :args [x (corpus/c 0.1)]}]}
                 :white {:op :abs :args [ring]}}
        positions (corpus/matrix 12 4)
        uvs (mapv (fn [i] (when (odd? i) [(* 0.1 i) (- 1.0 (* 0.05 i))])) (range 12))]
    (agree outputs {:beat 2.5} positions uvs)
    (agree outputs {:beat 2.5} positions nil)
    (agree outputs {:beat 2.5} (double-array (mapcat identity positions))
           (double-array (mapcat #(or % [0.5 0.5]) uvs)))
    (agree outputs {:beat 2.5} positions (assoc uvs 5 [0.1 Double/NaN]))))

(deftest batch-sharing-leaves-generated-glsl-unchanged
  (let [golden (edn/read-string (slurp (io/resource "afterglow/render/ir_glsl_golden.edn")))
        current (into {}
                      (concat
                       (for [{:keys [id outputs]} (corpus/families 100)
                             entry (cons [[id :batch] (ir/emit-glsl-batch outputs)]
                                         (for [[attribute e] outputs] [[id attribute] (ir/emit-glsl e)]))]
                         entry)
                       (for [[id e coordinates] corpus/shader-expressions] [[id coordinates] (ir/emit-glsl e coordinates)])
                       (for [[id outputs options] corpus/shader-batches]
                         [[id :batch options] (ir/emit-glsl-batch outputs options)])))]
    (is (= 31 (count golden)))
    (is (= (set (keys golden)) (set (keys current))))
    (doseq [[k emitted] golden]
      (is (= emitted (get current k)) (pr-str k)))))

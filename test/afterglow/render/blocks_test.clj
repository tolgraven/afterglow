(ns afterglow.render.blocks-test
  (:require [afterglow.render.blocks :as blocks]
            [afterglow.render.ir :as ir]
            [clojure.test :refer [deftest is testing]]))

(defn close? [a b] (< (abs (- a b)) 1.0e-10))

(deftest one-water-material-for-color-focus-and-dimmer
  (let [water {:block :optics/through-water}
        plan (blocks/plan {:base [0.8 0.7 0.3] :stages [water {:block :optics/gel}]})
        scalar (ir/compile-expression (:expression plan))
        trace (blocks/compile-trace plan)
        fields {:color (:expression plan)
                :focus (:expression (blocks/plan {:base 0.65 :stages [water]}))
                :dimmer (:expression (blocks/plan {:base 0.9 :stages [water]}))}
        batch (ir/compile-batch fields)
        shader (ir/emit-glsl-batch fields)
        positions [[1.0 0.0 0.4] [1.0 2.0 -0.3]]]
    (is (= 5 (:stride shader)))
    (is (re-find #"sin\(" (:source shader)))
    (doseq [beat [0.0 0.25 1.5]]
      (let [env {:elapsed-beats beat} result (ir/evaluate-batch batch env positions)
            colors (partition 3 (get-in result [:outputs :color :values]))]
        (doseq [[p rgb] (map vector positions colors)]
          (let [sample (trace (assoc env :position p))]
            (is (= [:optics/through-water :optics/gel] (mapv :block (:stages sample))))
            (is (= (scalar (assoc env :position p)) (:result sample)))
            (is (every? true? (map close? rgb (:result sample))))
            (is (every? true? (map close? (:result sample)
                                   (reduce #(mapv + %1 (:offset %2)) (:base sample) (:stages sample)))))))
        (is (not= (first colors) (second colors)))))))

(deftest middleware-preserves-context-and-runs-in-order
  (let [catalog (assoc blocks/library :show/lift {:mode :add :inputs {:by 0.1} :expression {:op :input :key :by}})
        chain [{:block :show/lift} {:block :optics/ribbed-glass :coordinates [0.0 1.0]}]
        apply-blocks (blocks/middleware catalog [:effect :private :focus] :number chain (constantly {}))
        context {:effect {:private {:focus 0.3}} :assignments [:keep]}
        result (apply-blocks context)]
    (is (close? 0.33 (get-in result [:effect :private :focus])))
    (is (= [:keep] (:assignments result)))
    (is (= 0.3 (get-in context [:effect :private :focus])))
    (is (thrown? Exception (blocks/plan {:base 0 :stages [{:block :missing}]})))
    (is (thrown? Exception (blocks/plan {:base 0 :stages [{:block :lfo/sine :inputs {:bogus 0.2}}]})))))

(deftest uv-mapping-ignores-depth-and-wet-zero-is-dry
  (let [water {:block :optics/through-water :coordinates :surface-uv}
        evaluate #(ir/compile-expression (:expression (blocks/plan {:base 1.0 :stages [%]})))
        a {:position [0.2 0.8 -9.0] :elapsed-beats 1.0}
        b (assoc a :position [0.2 0.8 11.0])]
    (is (= ((evaluate water) a) ((evaluate water) b)))
    (is (= 1.0 ((evaluate (assoc water :amount 0.0)) a)))))

(deftest calibrated-fog-uses-the-same-fragment-and-field
  (let [plan (blocks/plan {:base 0.8 :stages [{:block :optics/fog-transmission
                                               :inputs {:extinction 0.4 :density 0.25 :distance 10.0}}]})
        expression (:expression plan) expected (* 0.8 (Math/exp -1.0))
        result (ir/evaluate-batch (ir/compile-batch {:dimmer expression}) {} [[0 0 0]])]
    (is (close? expected (ir/evaluate expression {})))
    (is (close? expected (aget ^doubles (get-in result [:outputs :dimmer :values]) 0)))
    (is (= 1.0 (ir/evaluate (blocks/fog-transmission-expression -1.0 0.3 2.0) {})))
    (is (re-find #"in vec2 v_uv" (:source (ir/emit-glsl expression :surface-uv))))))

(deftest authored-glsl-runs-on-scalar-and-packed-fixture-fields
  (let [catalog (assoc blocks/library :custom/wave
                       {:mode :replace :inputs {:phase {:op :beat}}
                        :glsl "clamp(1.0 - 2.0 * abs(uv.x - .5) + sin(phase) / 4.0, 0., 1.)"})
        material (fn [catalog] (:expression (blocks/plan catalog {:base 0.0 :stages [{:block :custom/wave}]})))
        tree (material catalog)
        env {:elapsed-beats 0.5 :position [0.8 0.0 0.0]}
        expected (+ 0.4 (/ (Math/sin 0.5) 4.0))]
    (is (close? expected (ir/evaluate tree env)))
    (is (close? expected (first (get-in (ir/evaluate-batch (ir/compile-batch {:focus tree})
                                                          env [(:position env)]) [:outputs :focus :values]))))
    (doseq [bad ["phase; return 2." "unknownInput" "1.0 /* skip */" "sine(0.0)"
                 "clamp(1.0" "1+2 garbage" "" "uv.z"]]
      (is (thrown? Exception (material (assoc-in catalog [:custom/wave :glsl] bad)))))))

(deftest physical-and-surface-coordinates-can-contribute-to-the-same-native-field
  (let [catalog {:test/mix {:mode :replace :glsl "world.z + uv.x - uv.y + position.x"}}
        expr (:expression (blocks/plan catalog {:base 0 :stages [{:block :test/mix :coordinates :surface-uv}]}))
        fields {:focus expr}
        positions [[1.0 2.0 3.0] [1.0 2.0 3.0] [-2.0 4.0 5.0]]
        charts [[0.2 0.7] [1.1 -0.25] nil]
        expected [2.7 5.45 -3.0]
        plan (ir/compile-batch fields)
        values #(vec (get-in % [:outputs :focus :values]))
        fragment (ir/emit-glsl expr :surface-uv)
        charted (ir/emit-glsl-batch fields {:surface-uv? true})
        ordinary (ir/emit-glsl-batch fields)]
    (is (every? true? (map close? expected
                           (map #(ir/evaluate expr {:position %1 :surface-uv %2}) positions charts))))
    (is (every? true? (map close? expected (values (ir/evaluate-batch plan {} positions charts)))))
    (is (every? true? (map close? expected
                           (values (ir/evaluate-batch plan {} (double-array (mapcat identity positions))
                                                      (double-array [0.2 0.7 1.1 -0.25 -2 4]))))))
    (is (= [3.0 3.0 -3.0] (values (ir/evaluate-batch plan {} positions))))
    (is (re-find #"in vec3 v_position;" (:source fragment)))
    (is (re-find #"in vec2 v_uv;" (:source fragment)))
    (is (= "v_uv" (get-in charted [:inputs :surface-uv])))
    (is (nil? (get-in ordinary [:inputs :surface-uv])))
    (is (= {:position "v_position"}
           (:inputs (ir/emit-glsl-batch {:focus {:op :surface-uv :axis :u}}))))
    (is (not (re-find #"location = 1" (:source ordinary))))
    (is (thrown? clojure.lang.ExceptionInfo (ir/evaluate-batch plan {} positions [[1.0 2.0]])))
    (doseq [bad [[:bad 0] false]]
      (is (thrown? clojure.lang.ExceptionInfo (ir/evaluate-batch plan {} positions [bad nil nil]))))))

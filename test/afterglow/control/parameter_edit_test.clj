(ns afterglow.control.parameter-edit-test
  (:require [clojure.test :refer [deftest is]]
            [afterglow.control.parameter-edit :as edit]
            [afterglow.control.params :as params]))

(deftest explicit-schema-order-and-stable-fallback
  (is (= [:b :a :z :c]
         (edit/ordered-parameters {:param-order [:b :missing :b]
                                   :params {:z {:order 2} :a {:order 1} :c {} :b {}}}))))

(deftest numeric-fine-integer-and-boundaries
  (let [schema {:type :number :default 0 :bounds [-1 1]}]
    (is (= 0.2 (edit/edit schema 0 10 {}))))
  (is (= 0.02 (edit/edit {:type :number :default 0 :bounds [-1 1]} 0 10 {:fine? true})))
  (is (= 1 (edit/edit {:type :number :default 0 :bounds [-1 1]} 0 127 {})))
  (is (= 6 (edit/edit {:type :integer :default 3 :bounds [0 8]} 3 3 {:fine? true})))
  (is (= 8 (edit/edit {:type :integer :default 3 :bounds [0 8]} 3 1 {:mode :absolute})))
  (is (thrown? clojure.lang.ExceptionInfo
               (edit/edit {:type :number :default 0 :bounds [0 1]} 0 Double/NaN {}))))

(deftest boolean-and-waveform-values-do-not-coerce
  (is (true? (edit/edit {:type :boolean :default false} false 1 {})))
  (is (false? (edit/edit {:type :boolean :default true} true -1 {})))
  (let [sine {:signal-id :sine :version 1} saw {:signal-id :saw :version 4}
        schema {:type :enum :default sine :values [sine saw] :widget :waveform}]
    (is (= saw (edit/edit schema sine 1 {})))
    (is (= saw (edit/edit schema saw 6 {})))
    (is (= sine (edit/edit schema saw 0 {:mode :absolute})))))

(deftest component-editing-preserves-other-components-and-range-order
  (let [vector-schema {:type :vector :size 3 :default [0 0 0] :bounds [-10 10]}
        range-schema {:type :range :default [2 7] :bounds [0 10]}]
    (is (= [0 0.2 0] (edit/edit vector-schema [0 0 0] 1 {:component 1})))
    (is (= [0 0 10] (edit/edit vector-schema [0 0 0] 1 {:component 2 :mode :absolute})))
    (is (= [7 7] (edit/edit range-schema [2 7] 127 {})))
    (is (= [2 2] (edit/edit range-schema [2 7] -127 {:component 1})))
    (is (= [2.1 7] (edit/edit range-schema [2 7] 1 {})))
    (doseq [component [0 1] input [-100 -1 0 1 100]]
      (is (params/valid-value? range-schema (edit/edit range-schema [2 7] input {:component component}))))))

(deftest hsv-color-editing-and-grid-extremes
  (let [schema {:type :color :default [1 0 0]}]
    (is (= [0.0 1.0 1.0] (edit/edit schema [1 0 0] 0.5 {:component 0 :mode :absolute})))
    (is (= [1.0 1.0 1.0] (edit/edit schema [1 0 0] 0 {:component 1 :mode :absolute})))
    (is (= [0.0 0.0 0.0] (edit/edit schema [1 0 0] 0 {:component 2 :mode :absolute})))
    (is (= [0.0 0.0 0.0] (edit/color-grid-value 0 0)))
    (is (= [1.0 1.0 1.0] (edit/color-grid-value 7 0)))
    (doseq [x (range 8) y (range 8)]
      (is (params/valid-value? schema (edit/color-grid-value x y))))))

(deftest velocity-maps-only-opted-in-numeric-parameters-with-valid-endpoints
  (let [definition {:params {:level {:type :number :default 0 :bounds [0 1] :velocity true
                                     :velocity-min 0.2 :velocity-max 0.8}
                             :count {:type :integer :default 2 :bounds [1 8] :velocity true
                                     :velocity-min 8 :velocity-max 1}
                             :free {:type :integer :default 50 :velocity true
                                    :velocity-min 40 :velocity-max 80}
                             :static {:type :number :default 0 :bounds [0 1]}
                             :flag {:type :boolean :default true :velocity true}}}]
    (is (= {:level 0.2 :count 8 :free 40} (edit/velocity-values definition 0)))
    (is (= {:level 0.5 :count 5 :free 60} (edit/velocity-values definition 0.5)))
    (is (= 1 (:count (edit/velocity-values definition 1))))
    (is (= (edit/velocity-values definition 1) (edit/velocity-values definition 9))))
  (let [definition {:params {:fractional-bounds {:type :integer :default 2 :bounds [1.2 7.8] :velocity true}}}]
    (is (= {:fractional-bounds 2} (edit/velocity-values definition 0)))
    (is (= {:fractional-bounds 7} (edit/velocity-values definition 1))))
  (is (thrown? clojure.lang.ExceptionInfo (edit/velocity-values {} Double/NaN))))

(deftest normalized-control-feedback-round-trips-typed-component-values
  (doseq [[schema value component] [[{:type :number :bounds [-1 1]} 0.25 0]
                                     [{:type :integer :bounds [0 16]} 11 0]
                                     [{:type :boolean} true 0]
                                     [{:type :boolean} false 0]
                                     [{:type :enum :values [:one :two :three]} :two 0]
                                     [{:type :enum :values [:one]} :one 0]
                                     [{:type :vector :size 2 :bounds [-1 1]} [0.25 0.5] 1]
                                     [{:type :range :bounds [0 10]} [2.0 7.0] 0]
                                     [{:type :range :bounds [0 10]} [2.0 7.0] 1]]]
    (is (= value (edit/edit schema value (edit/position schema value {:component component})
                            {:component component :mode :absolute}))))
  (is (= 0.5 (edit/position {:type :color} [0 1 1] {:component 0})))
  (is (= 0.0 (edit/position {:type :number :bounds [4 4]} 4 {}))))

(deftest explicitly-unbounded-velocity-uses-normalized-range
  (is (= {:level 0.5}
         (edit/velocity-values {:params {:level {:type :number :bounds nil :default 0 :velocity true}}} 0.5))))

(deftest bounded-colors-remain-adjustable-with-encoders-touch-and-grid
  (doseq [[lo hi] [[0.0 0.5] [0.2 0.7] [0.4 0.4]]]
    (let [schema {:type :color :bounds [lo hi] :default [hi lo lo]}
          value (:default schema)]
      (is (= value (edit/edit schema value 2 {:component 2})))
      (doseq [x (range 8) y (range 8)]
        (is (params/valid-value? schema (edit/color-grid-value schema x y))))
      (doseq [v [0.0 0.5 1.0]]
        (let [rgb (edit/edit schema value v {:mode :absolute :component 2})]
          (is (params/valid-value? schema rgb))
          (when (< lo hi)
            (is (< (abs (- v (edit/position schema rgb {:component 2}))) 1e-8))))))))

(deftest explicitly-unbounded-colors-use-the-full-control-range
  (let [schema {:type :color :bounds nil :default [1 0 0]}]
    (is (= [0.5 0.0 0.0] (edit/edit schema [1 0 0] 0.5 {:mode :absolute :component 2})))
    (is (== 1 (edit/position schema [1 0 0] {:component 2})))
    (is (= (edit/color-grid-value 3 4) (edit/color-grid-value schema 3 4)))))

(deftest gradients-are-not-scalar-edited-by-controls
  (let [schema {:type :gradient :default [{:position 0 :color [1 0 0]} {:position 1 :color [0 0 1]}]}
        value (:default schema)]
    (is (= [:value] (edit/components schema)))
    (is (= value (edit/edit schema value 5 {})))
    (is (= value (edit/edit schema value 0.7 {:mode :absolute})))
    (is (= 0.0 (edit/position schema value {})))
    (is (thrown? clojure.lang.ExceptionInfo (edit/edit schema [] 1 {})))
    (is (thrown? clojure.lang.ExceptionInfo (edit/position schema [] {})))))

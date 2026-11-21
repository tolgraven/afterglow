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

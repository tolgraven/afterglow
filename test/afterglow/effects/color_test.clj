(ns afterglow.effects.color-test
  (:require [clojure.test :refer :all]
            [afterglow.effects.color :refer :all]
            [afterglow.effects.params :as params]
            [afterglow.show-context :refer [with-show]]
            [afterglow.channels :as channels]
            [com.evocomputing.colors :as colors]
            [thi.ng.color.core :as clr]
            [afterglow.effects :as fx]
            [afterglow.fixtures.chauvet :as chauvet]
            [taoensso.timbre :as timbre :refer [error warn info debug spy]]))

(deftest test-extract-rgb
  (testing "Finding RGB color channels")
  (is (= [:12-channel] (map :mode (channels/find-rgb-heads [(chauvet/slimpar-hex3-irc)])))))

(deftest htp-assigner-retains-higher-components-from-earlier-effects
  (let [head {:id :test}
        current (clr/rgba 0.2 0.8 0.1)
        previous (clr/rgba 0.9 0.1 0.7)
        assigner (build-htp-color-assigner head current {} {})
        result (fx/assign assigner {} {} head previous)]
    (is (= [0.9 0.8 0.7 1.0] @(clr/as-rgba result)))
    (is (= current (fx/assign assigner {} {} head nil)))))

(deftest color-builder-uses-one-representation-for-constant-and-dynamic-components
  (let [show {:variables (atom {:blue 255})}]
    (with-show show
      (is (= [0.0 0.0 0.0 1.0] @(clr/as-rgba (params/build-color-param))))
      (is (= [0.0 1.0 0.0 1.0] @(clr/as-rgba (params/build-color-param :color "red" :h 120 :s 100 :l 50))))
      (let [p (params/build-color-param :color "red" :b :blue)]
        (is (= thi.ng.color.core.HSLA (params/result-type p)))
        (is (every? #(< (Math/abs (double %)) 1.0e-6)
                    (map - [1 0 1 1] @(clr/as-rgba (params/evaluate p show nil nil)))))))))

(deftest color-wheel-uses-degrees-and-percentage-across-the-hue-boundary
  (let [show {:variables (atom {}) :movement (atom {})}
        channel {:universe 1 :index 0}
        target {:id :wheel :color-wheel-hue-map {0 [channel {:start 26 :end 26}]
                                                 240 [channel {:start 124 :end 124}]}}
        sample (fn [degrees saturation]
                 (let [buffer (byte-array 1)]
                   (with-show show
                     (fx/resolve-assignment {:kind :color :target target :value (clr/hsla (/ degrees 360) saturation 0.5)}
                                            show {} {1 buffer}))
                   (bit-and 255 (aget buffer 0))))]
    (is (= 124 (sample 240 1)))
    (is (= 26 (sample 359 1)))
    (is (zero? (sample 240 0.1)))))

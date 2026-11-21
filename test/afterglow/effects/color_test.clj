(ns afterglow.effects.color-test
  (:require [clojure.test :refer :all]
            [afterglow.effects.color :refer :all]
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

(ns afterglow.render.photometry-test
  (:require [clojure.test :refer [deftest is]]
            [afterglow.render.frame :as frame]
            [afterglow.render.photometry :as photometry]))

(def spot {:id :spot :address 1 :universe 1 :channels {:red 1 :green 2 :blue 3}})

(deftest optical-properties-survive-physical-patching
  (let [props {:beam-angle 14.5 :lens-radius-m 0.05 :zoom-range-deg [35 10]
               :max-watts 120 :measured-relative-brightness 1.25 :pseudo-fixture false}]
    (is (= props (select-keys (first (:fixtures (frame/compile-patch [(merge spot props)])))
                              photometry/fixture-keys)))
    (is (empty? (photometry/errors spot)))
    (doseq [[key value] [[:beam-angle nil] [:beam-angle 0] [:beam-angle 180] [:beam-angle ##Inf]
                         [:max-watts -10] [:measured-relative-brightness ##NaN] [:pseudo-fixture "yes"]
                         [:zoom-range-deg [2 180]] [:lens-radius-m 0]]]
      (is (= [:fixtures 1 key] (:path (first (frame/validate-patch [spot (assoc spot :id :bad :address 4 key value)]))))))))

(deftest full-white-measurements-and-estimates
  (let [estimate #(photometry/relative-brightness (assoc spot :max-watts %))]
    (is (== 1 (estimate 100)))
    (is (== 0.5 (estimate 50)))
    (is (== 1 (photometry/relative-brightness spot)))
    (is (< (photometry/relative-brightness (-> spot (assoc :max-watts 100) (assoc-in [:channels :uv] 4))) 1))
    (is (zero? (photometry/relative-brightness {:max-watts 100 :channels {:uv 1 :dimmer 2}})))
    (is (== 2.2 (photometry/relative-brightness (assoc spot :max-watts 20 :measured-relative-brightness 2.2))))))

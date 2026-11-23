(ns afterglow.output.timeline-test
  (:require [afterglow.output.timeline :as t]
            [clojure.test :refer [deftest is]]))

(deftest target-slots-and-real-input-headroom-after-cold-or-slow-work
  (let [grid (t/timeline 0 25)
        cold (t/next-render grid 0)
        first (t/observed grid cold 0 10 12)
        next (t/next-render first 12)
        sampled (t/observed first next 39.2 44.2 45)]
    (is (== 25 (:deadline-ms cold)))
    (is (== 39 (:start-at-ms next)))
    (is (== 50 (:deadline-ms next)))
    (is (= 2 (:on-time sampled)))
    (is (< 5.7 (get-in sampled [:last :slack-ms]) 5.9))
    (is (= 4 (t/next-output-slot grid 2 74 79)) "Skip the impending 75 ms send after a severely late wake")
    (let [late (t/observed grid cold 0 60 61)
          t2 (t/next-render late 61)
          slower (t/observed late t2 (:start-at-ms t2) (+ 60 (:start-at-ms t2)) (+ 62 (:start-at-ms t2)))
          recovered (t/next-render slower (get-in slower [:last :finished-at-ms]))]
      (is (zero? (:on-time slower)))
      (is (> (:lead-ms recovered) 60))
      (is (> (:slot recovered) (:slot t2)))
      (is (>= (:start-at-ms recovered) (get-in slower [:last :finished-at-ms]))))))

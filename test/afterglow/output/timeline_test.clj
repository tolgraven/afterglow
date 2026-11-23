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

(deftest a-late-wake-increases-reserve-even-if-the-effect-could-not-run
  (let [cold (t/timeline 0 25)
        warm (t/observed cold (t/next-render cold 0) 0 0.3 1)
        late (t/next-render warm 1)
        woke (+ (:start-at-ms late) 2)
        after (t/missed-wake warm late woke)
        retry (t/next-render after woke)]
    (is (> woke (:deadline-ms late)))
    (is (= 1 (:renders after)))
    (is (= 1 (:missed-wakes after)))
    (is (= 1 (:skipped after)))
    (is (< (+ (:start-at-ms retry) 2 0.3) (:deadline-ms retry))
        "The same OS wake delay must leave time for the next short effect")))

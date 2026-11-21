(ns afterglow.rhythm-test
  (:require [clojure.test :refer :all]
            [afterglow.rhythm :as rhythm]))

(deftest beat-boundaries-and-pre-roll-have-consistent-phases
  (is (= 500 (rhythm/beat-ms 1 120)))
  (doseq [[instant number phase] [[999 0 0.998]
                                  [1000 1 0.0]
                                  [1250 1 0.5]
                                  [1499 1 0.998]
                                  [1500 2 0.0]]]
    (is (= number (rhythm/marker-number instant 1000 500)))
    (is (< (Math/abs (- phase (rhythm/marker-phase instant 1000 500))) 1.0e-9))))

(deftest musical-ratios-cycle-across-marker-boundaries
  (is (= 0.25 (rhythm/enhanced-phase 1 0.5 2)))
  (is (= 0.75 (rhythm/enhanced-phase 2 0.5 2)))
  (is (= 0.25 (rhythm/enhanced-phase 3 0.5 2)))
  (is (= 0.5 (rhythm/enhanced-phase 1 0.25 1/2)))
  (is (= 0.5 (rhythm/enhanced-phase 1 0.75 1/2))))

(deftest snapshots-encode-beat-bar-and-phrase-positions
  (let [snapshot (rhythm/->MetronomeSnapshot 0 120 4 4 2625 6 2 1 0.25 0.3125 0.328125)]
    (is (= 2 (rhythm/snapshot-beat-within-bar snapshot)))
    (is (= 6 (rhythm/snapshot-beat-within-phrase snapshot)))
    (is (= 2 (rhythm/snapshot-bar-within-phrase snapshot)))
    (is (= "1.2.2" (rhythm/snapshot-marker snapshot)))
    (is (false? (rhythm/snapshot-down-beat? snapshot)))
    (is (false? (rhythm/snapshot-phrase-start? snapshot)))))

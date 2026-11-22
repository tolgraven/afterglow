(ns afterglow.render.atmosphere.calibration-test
  (:require [afterglow.render.atmosphere :as fog]
            [afterglow.render.atmosphere.calibration :as calibration]
            [afterglow.render.frame :as frame]
            [clojure.test :refer [deftest is]]))

(def rig (frame/compile-patch [{:id :nozzle :universe 1 :address 1 :channels {:fog 1}
                                :fogger {:flow-m3-min 60 :mixing-seconds 3}}]))
(def plan (fog/plan {:width 2 :height 2 :depth 5 :fog-half-life-s 180 :air-changes-per-hour 50
                     :measured-fog {:clearance-half-life-s 18 :extinction-per-m 2.1 :reference-path-m 3}} rig))

(defn recording []
  (let [ts (range 0 85000 1000)
        states (rest (reductions #(fog/present plan %1 %2 {1 [(if (<= 5000 %2 12000) 255 0)]})
                                 (fog/initial plan 1 0) ts))]
    {:samples (mapv (fn [t s] {:elapsed-ms t :bright (+ 0.05 (* 0.75 (- 1 (:fog-level s)))) :dark 0.05
                               :phase (cond (< t 5000) :baseline (< t 13000) :active :else :clearing)}) ts states)
     :flows [{:elapsed-ms 5000 :flow-m3-s 1.0} {:elapsed-ms 13000 :flow-m3-s 0.0}]
     :volume-m3 20 :path-m 3}))

(deftest recover-room-and-fluid-properties-from-a-stationary-sightline
  (let [data (recording) fit (calibration/fit data)
        tail (calibration/fit (dissoc data :flows))]
    (is (< (abs (- (:clearance-half-life-s fit) 18)) 0.4))
    (is (< (abs (- (:mixing-seconds fit) 3)) 0.15))
    (is (< (abs (- (:extinction-per-m fit) 2.1)) 0.08))
    (is (> (:r-squared fit) 0.999))
    (is (= :clearance-tail (:method tail)))
    (is (nil? (:extinction-per-m tail)))
    (is (< (abs (- (:clearance-half-life-s tail) 18)) 1.2))
    (is (thrown? Exception (calibration/fit (update data :samples subvec 0 12))))
    (is (thrown? Exception (calibration/fit (assoc-in data [:samples 0 :bright] 0.3))))))

(deftest exposure-and-freshness-come-from-the-calibrated-physical-model
  (let [room (fog/reconfigure plan {:mixed-m3 5.0 :sources []} 1 0 true)
        a (fog/present plan room 10 {1 [0]})
        b (fog/present plan a 18010 {7 [0]})]
    (is (< (abs (- (:mixed-m3 b) 2.5)) 0.002))
    (is (= 10 (:last-presented-ms b) (get-in b [:sources 0 :last-presented-ms])))
    (is (< (abs (- (:fog-level b) (- 1 (Math/exp (- (* (/ (:mixed-m3 b) 20) 2.1 3)))))) 1e-9))))

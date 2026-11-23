(ns afterglow.runtime.cadence-test
  (:require [afterglow.runtime.cadence :as cadence]
            [clojure.test :refer [deftest is testing]]))

(def opts (cadence/settings {:pressure-frames 2 :recovery-frames 3 :smoothing 0.5}))
(def version {:a 1 :b 1 :cheap 1 :external 1})

(defn- cost [ms eligible?]
  {:calls 1 :total-ms ms :predictive? eligible?})

(def costs {:a (cost 8 true) :b (cost 7 true) :cheap (cost 0.1 true) :external (cost 40 false)})

(defn- tick [state ms]
  (cadence/advance state {:epoch 1 :versions version :samples costs :elapsed-ms ms :period-ms 25} opts))

(deftest expensive-predictable-effects-share-pressure-and-recover
  (let [states (vec (take 10 (iterate #(tick % 29) nil)))]
    (is (empty? (:keyframe-intervals (states 1))))
    (is (= {:a {:ms 50}} (:keyframe-intervals (states 2))))
    (is (= {:a {:ms 50} :b {:ms 50}} (:keyframe-intervals (states 4))))
    (is (not-any? #{:cheap :external} (keys (:keyframe-intervals (peek states)))))
    (is (every? #(<= (:ms %) 200) (vals (:keyframe-intervals (peek states)))))
    (let [after (take 35 (iterate #(tick % 3) (peek states)))]
      (is (= (:keyframe-intervals (peek states)) (:keyframe-intervals (second after))))
      (is (empty? (:keyframe-intervals (last after)))))))

(deftest time-and-version-boundaries
  (let [warm (nth (iterate #(tick % 30) nil) 6)
        options {:epoch 1 :versions {:a 2 :unset nil} :period-ms 25 :elapsed-ms 3 :samples {}}
        changed (cadence/advance warm options opts)
        fresh (cadence/advance warm (assoc options :epoch 2) opts)]
    (is (= #{:a :unset} (set (keys (:effects changed)))))
    (is (empty? (:keyframe-intervals changed)))
    (is (= 1 (get-in changed [:effects :unset :stride])))
    (is (= 1 (:frame fresh)))
    (is (nil? (get-in changed [:effects :a :cost-ms])))
    (is (thrown? clojure.lang.ExceptionInfo (cadence/settings {:headroom 1})))
    (is (thrown? clojure.lang.ExceptionInfo (cadence/advance nil (assoc options :period-ms 0) opts)))))

(deftest observer-preserves-results-and-faults-under-concurrency
  (let [{:keys [measure-effect samples]} (cadence/observer)
        calls (mapv (fn [i] (future (measure-effect :layer true (constantly i)))) (range 8))]
    (is (= (vec (range 8)) (mapv deref calls)))
    (is (thrown? ArithmeticException (measure-effect :layer true #(/ 1 0))))
    (is (= 9 (get-in @samples [:layer :calls])))
    (is (>= (get-in @samples [:layer :total-ms]) 0)))
  (let [time (atom 0)
        {:keys [measure-effect samples]} (cadence/observer #(swap! time + 4000000))]
    (is (= :result (measure-effect :io false (constantly :result))))
    (is (= {:io {:calls 1 :predictive? false :total-ms 4.0}} @samples))))

(deftest ranks-real-evaluations-and-applies-live-stride-limits
  (let [warm (nth (iterate #(tick % 29) nil) 8)
        limited (cadence/advance warm {:epoch 1 :versions version :samples {}
                                       :elapsed-ms 8 :period-ms 25}
                                 (assoc opts :max-stride 1))
        ranking (cadence/ranked-costs limited)]
    (is (= [:external :a :b :cheap] (mapv :instance-id ranking)))
    (is (every? #(= 8 (:evaluations %) (:sampled-frames %)) ranking))
    (is (empty? (:keyframe-intervals limited)))))

(deftest warmup-spikes-and-later-cheap-effects-under-pressure
  (let [config (cadence/settings {:pressure-frames 1 :min-cost-ms 0.5})
        step (fn [state cost-ms]
               (cadence/advance state {:epoch 1 :versions {:effect 1} :period-ms 25 :elapsed-ms 35
                                       :samples (if cost-ms {:effect (cost cost-ms true)} {})} config))
        spike (step nil 12)
        expensive (step spike 5)
        still-expensive (step expensive nil)
        cheap-once (step still-expensive 0.1)
        interpolated (step cheap-once nil)
        cheap-twice (step interpolated 0.2)]
    (is (empty? (:keyframe-intervals spike)))
    (is (> (get-in expensive [:effects :effect :stride]) 1))
    (is (= (:keyframe-intervals expensive) (:keyframe-intervals still-expensive)))
    (is (> (get-in interpolated [:effects :effect :stride]) 1))
    (is (empty? (:keyframe-intervals cheap-twice)))
    (is (> (:frame-ms cheap-twice) 25))
    (is (> (get-in cheap-twice [:effects :effect :cost-ms]) 0.5))
    (is (empty? (:keyframe-intervals (step cheap-twice 15))))))

(deftest live-cost-floor-reclassifies-a-slowed-instance
  (let [state (nth (iterate #(tick % 35) nil) 6)
        frame {:epoch 1 :versions version :samples {} :elapsed-ms 35 :period-ms 25}]
    (is (seq (:keyframe-intervals state)))
    (is (empty? (:keyframe-intervals (cadence/advance state frame (assoc opts :min-cost-ms 10)))))))

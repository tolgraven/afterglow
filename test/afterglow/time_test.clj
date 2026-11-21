(ns afterglow.time-test
  (:require [clojure.test :refer [deftest is]] [afterglow.time :as time]))

(deftest musical-values-and-meter
  (is (= 1/2 (time/duration->beats {:beats 1/2})))
  (is (= 0.5 (time/duration->beats {:beats 0.5})))
  (is (= 6 (time/duration->beats {:bars 2} {:beats-per-bar 3})))
  (is (= 24 (time/duration->beats {:phrases 2} {:beats-per-bar 3 :bars-per-phrase 4})))
  (is (= {:beats-per-bar 4 :bars-per-phrase 4} (time/normalize-meter nil)))
  (is (thrown? clojure.lang.ExceptionInfo (time/duration->beats {:ms 500})))
  (doseq [duration [nil {} {:seconds 1} {:beats 1 :bars 1} {:beats -1}
                    {:bars ##NaN} {:phrases ##Inf} {:beats "1/2"}]]
    (is (seq (time/validate-duration duration))))
  (is (empty? (time/validate-duration {:beats 0})))
  (is (thrown? clojure.lang.ExceptionInfo (time/normalize-meter {:beats-per-bar 0}))))

(deftest musical-timers-use-transport-and-capture-meter
  (let [timer (time/start {:bars 2} {:time-ms 100 :beat 8 :bpm 120 :meter {:beats-per-bar 3}})]
    (is (= 6 (get-in timer [:duration :value])))
    (is (= 0.5 (:progress (time/sample timer {:time-ms 1600 :beat 11 :bpm 240}))))
    (is (= 0.5 (:progress (time/sample timer {:time-ms 99999 :beat 11 :playing? false}))))
    (is (false? (:done? (time/sample timer {:beat 13 :meter {:beats-per-bar 7}}))))
    (is (:done? (time/sample timer {:beat 14})))
    (is (= 0 (:remaining (time/sample timer {:beat 16}))))
    (is (= 3000.0 (time/estimate-ms (:duration timer) 120)))
    (is (= 1500.0 (time/estimate-ms (:duration timer) 240)))))

(deftest explicit-millisecond-compatibility
  (let [timer (time/start {:ms 500} 100)]
    (is (= 0.5 (:progress (time/sample timer 350))))
    (is (:done? (time/sample timer {:time-ms 600 :beat 0 :playing? false}))))
  (is (= {:time-ms 100 :beat 4 :bpm 120 :playing? false}
         (time/frame-clock {:time-ms 100 :transport {:beat 4 :bpm 120 :playing? false}})))
  (is (thrown? clojure.lang.ExceptionInfo (time/start {:beats 1} 0)))
  (is (:done? (time/sample (time/start {:beats 0} {:beat 1}) {:beat 1})))
  (is (false? (:done? (time/sample (time/start {:beats 0} {:beat 1}) {:beat 0})))))


(deftest fractional-meter-counts-quarter-note-beats-and-retains-exact-ratios
  (is (= {:beats-per-bar 7/2 :bars-per-phrase 4}
         (time/normalize-meter {:beats-per-bar 7/2})))
  (is (= 7 (time/duration->beats {:bars 2} {:beats-per-bar 7/2})))
  (is (= 7/4 (time/duration->beats {:bars 1/2} {:beats-per-bar 7/2})))
  (is (= 28 (time/duration->beats {:phrases 2} {:beats-per-bar 7/2 :bars-per-phrase 4})))
  (let [timer (time/start {:bars 2} {:beat 8.0 :time-ms 0 :meter {:beats-per-bar 3.5}})]
    (is (= 7.0 (get-in timer [:duration :value])))
    (is (= 0.5 (:progress (time/sample timer {:beat 11.5 :time-ms 1000 :bpm 240}))))
    (is (= 0.5 (:progress (time/sample timer {:beat 11.5 :time-ms 90000 :playing? false}))))
    (is (false? (:done? (time/sample timer {:beat 14.999 :meter {:beats-per-bar 4}}))))
    (is (:done? (time/sample timer {:beat 15.0 :meter {:beats-per-bar 4}})))
    (is (= 3500.0 (time/estimate-ms (:duration timer) 120)))
    (is (= 1750.0 (time/estimate-ms (:duration timer) 240))))
  (doseq [beats [0 -1 ##NaN ##Inf "7/8"]]
    (is (thrown? clojure.lang.ExceptionInfo (time/normalize-meter {:beats-per-bar beats}))))
  (doseq [bars [0 -1 1/2 2.5 ##NaN ##Inf]]
    (is (thrown? clojure.lang.ExceptionInfo
                 (time/normalize-meter {:beats-per-bar 3.5 :bars-per-phrase bars})))))

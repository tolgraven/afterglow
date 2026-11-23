(ns afterglow.render.easing-test
  (:require [clojure.test :refer [deftest is]]
            [afterglow.render.easing :as easing]))

(defn- close? [x y] (< (abs (- x y)) 1.0e-8))

(deftest css-bezier-inverts-time-and-retains-overshoot
  (let [identity-curve {:type :cubic-bezier :points [1 1 0 0]}
        overshoot {:type :cubic-bezier :points [0.15 1.9 0.85 1.05]}]
    (doseq [x [0.0002 0.2 0.49 0.5 0.6 0.9999]] (is (close? x (easing/sample identity-curve x))))
    (is (> (easing/sample overshoot 0.5) 1.0))
    ;; x(t)=t^3, y(t)=1-(1-t)^3. At t=0.5 the input is 0.125.
    (is (close? 0.875 (easing/sample {:type :cubic-bezier :points [0 1 0 1]} 0.125)))))

(deftest springs-and-easings-use-absolute-progress
  (let [underdamped (easing/evaluator {:type :spring :frequency 1.5 :damping 0.15})]
    (is (> (underdamped 0.33) 1.0))
    (is (= (mapv underdamped [0.5 0.2]) (reverse (mapv underdamped [0.2 0.5])))))
  (doseq [curve [:step :linear :ease-in-out :sine :smoothstep :spring
                 {:type :spring :frequency 2 :damping 0}
                 {:type :spring :frequency 16 :damping 8} {:type :spring :damping 1}]]
    (let [f (easing/evaluator curve)]
      (is (= [0.0 0.0 1.0 1.0] (mapv f [-1 0 1 2])))
      (is (every? #(Double/isFinite (f (/ % 128.0))) (range 129)))))
  (doseq [curve [{:type :cubic-bezier :points [1 -3 2 0]} {:type :power :exponent 0}
                 {:type :spring :frequency 0} {:type :spring :damping ##NaN}]]
    (is (thrown? clojure.lang.ExceptionInfo (easing/evaluator curve))))
  (is (thrown? clojure.lang.ExceptionInfo (easing/sample :linear ##NaN))))

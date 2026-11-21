(ns afterglow.effects.pipeline-test
  (:require [clojure.test :refer :all]
            [afterglow.effects :as fx]))

(deftest assigners-compose-in-order-and-receive-explicit-context
  (let [show {:id :test-show}
        snapshot {:instant 1234}
        target {:id 42}
        observed (atom [])
        assigner (fn [f]
                   (fx/build-head-assigner
                    :test target
                    (fn [s snap head previous]
                      (swap! observed conj [s snap head previous])
                      (f previous))))
        add (assigner #(+ % 3))
        multiply (assigner #(* % 2))]
    (is (= (fx/->Assignment :test 42 target 14)
           (fx/run-assigners show snapshot [add multiply] 4)))
    (is (= [[show snapshot target 4] [show snapshot target 7]] @observed))
    (is (= 11 (:value (fx/run-assigners show snapshot [multiply add] 4))))))

(deftest empty-and-nil-assignments-have-distinct-meaning
  (let [target {:id 8}
        nil-assigner (fx/build-head-assigner :test target (fn [_ _ _ _] nil))]
    (is (nil? (fx/run-assigners {} {} [] 12)))
    (is (= (fx/->Assignment :test 8 target nil)
           (fx/run-assigners {} {} [nil-assigner] 12)))))

(deftest scenes-retain-order-and-remove-finished-children
  (let [left (fx/->Effect "Left" fx/always-active (fn [_ _] [:left]) fx/end-immediately)
        right (fx/->Effect "Right" (fn [_ snapshot] (< (:instant snapshot) 2))
                           (fn [_ _] [:right]) fx/end-immediately)
        scene (fx/scene "Pair" left right)]
    (is (true? (fx/still-active? scene {} {:instant 1})))
    (is (= [:left :right] (vec (fx/generate scene {} {:instant 1}))))
    (is (true? (fx/still-active? scene {} {:instant 2})))
    (is (= [:left] (vec (fx/generate scene {} {:instant 2}))))
    (is (true? (fx/end scene {} {:instant 2})))
    (is (false? (fx/still-active? scene {} {:instant 3})))
    (is (empty? (fx/generate scene {} {:instant 3})))))

(deftest scene-graceful-ending-retains-only-releasing-children
  (let [immediate (fx/blank "Immediate")
        releasing (fx/->Effect "Release" (fn [_ snapshot] (< (:instant snapshot) 10))
                               (fn [_ _] [:release]) (fn [_ _] false))
        scene (fx/scene "Release pair" immediate releasing)]
    (is (false? (fx/end scene {} {:instant 5})))
    (is (= [:release] (vec (fx/generate scene {} {:instant 5}))))
    (is (false? (fx/still-active? scene {} {:instant 10})))
    (is (empty? (fx/generate scene {} {:instant 10})))))

(deftest code-effects-run-once-during-sequential-lifecycle-checks
  ;; This deliberately does not assert exactly-once behavior under contention:
  ;; the current implementation invokes user code inside swap!, which may retry.
  (let [calls (atom [])
        effect (fx/code (fn [show snapshot] (swap! calls conj [show snapshot])))]
    (is (true? (fx/still-active? effect {:id 1} {:instant 1})))
    (is (true? (fx/still-active? effect {:id 1} {:instant 2})))
    (is (= [[{:id 1} {:instant 1}]] @calls))
    (is (empty? (fx/generate effect {} {})))
    (is (true? (fx/end effect {} {})))))

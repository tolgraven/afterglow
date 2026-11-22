(ns afterglow.runtime.reuse-test
  (:require [afterglow.render.ir :as ir]
            [afterglow.runtime :as runtime]
            [afterglow.runtime.reuse :as reuse]
            [clojure.test :refer [deftest is testing]]))

(deftest declared-reads-are-injected-and-unrelated-frame-changes-do-not-run-the-step
  (let [calls (atom 0)
        step (reuse/step {:pure? true :inputs [[:frame :beat] [:frame :variables :level]
                                               [:state :counter] [:instance :params :gain]]}
                         (fn [{:keys [frame state instance] :as captured}]
                           (swap! calls inc)
                           (is (= #{:frame :state :instance} (set (keys captured))))
                           (is (not (contains? frame :time-ms)))
                           {:assignments [[(:beat frame) (get-in frame [:variables :level])
                                           (:counter state) (get-in instance [:params :gain])]]
                            :intents [:pulse]}))
        descriptor {:id :a :order 0 :priority 0 :state {:counter 0} :step step :instance {:params {:gain 1}}}
        context {:frame {:time-ms 0 :beat 2 :variables {:level 0.5}} :effects [descriptor]}
        run #(runtime/render-frame %)
        baseline (run context)]
    (is (= [[2 0.5 0 1]] (:assignments baseline)))
    (is (= [:pulse] (:intents (run (assoc-in context [:frame :time-ms] 90)))))
    (is (= 1 @calls))
    (doseq [[path value] [[[:frame :beat] 3] [[:frame :variables :level] 0.75]
                          [[:effects 0 :state :counter] 3] [[:effects 0 :instance :params :gain] 0.25]]]
      (run (assoc-in context path value)))
    (is (= 5 @calls))
    (let [other (assoc-in context [:effects 0 :step]
                          (reuse/step {:pure? true :inputs []} (constantly {:assignments [:reloaded]})))]
      (is (= [:reloaded] (:assignments (run other)))))))

(deftest purity-is-explicit-and-failures-retry
  (doseq [[pure? count-expected] [[false 3] [true 2]]]
    (let [n (atom 0)
          evaluate (reuse/evaluator {:pure? pure? :inputs []}
                                    (fn [_] (when (= 1 (swap! n inc)) (throw (ex-info "retry me" {}))) :ok))]
      (is (thrown? Exception (evaluate {})))
      (is (= :ok (evaluate {})))
      (is (= :ok (evaluate {})))
      (is (= count-expected @n))))
  (let [n (atom 0)
        step (reuse/step {:pure? true :inputs []} (fn [_] {:assignments (swap! n inc)}))]
    (dotimes [_ 2] (is (thrown? Exception (step {}))))
    (is (= 2 @n))))

(deftest stable-keys-preserve-numeric-representation-and-absent-values
  (let [calls (atom 0)
        calc (reuse/evaluator {:pure? true :inputs [[:v]]} (fn [_] (swap! calls inc)))]
    (doseq [v [{} {:v nil} {:v 0.0} {:v -0.0} {:v [1N]} {:v [1]} {:v 1.0M} {:v 1.00M}]]
      (let [n @calls] (is (= (inc n) (calc v) (calc v)))))
    (is (= 8 @calls))))

(deftest independent-arrays-mutable-inputs-and-bounded-retention
  (let [calls (atom 0)
        calc (reuse/evaluator {:pure? true :inputs [[:v]] :max-values 12}
                              (fn [_] (swap! calls inc) {:values (double-array [1.0 2.0])}))
        first-array (:values (calc {:v 1}))]
    (aset-double first-array 0 50.0)
    (let [second-array (:values (calc {:v 1}))]
      (is (= [1.0 2.0] (vec second-array)))
      (aset-double second-array 1 -7.0))
    (is (= [1.0 2.0] (vec (:values (calc {:v 1})))))
    (is (= 1 @calls))
    (doseq [v [(atom 0) (byte-array 2) (vec (range 14))]]
      (calc {:v v}) (calc {:v v}))
    (is (= 7 @calls))))

(deftest overlapping-submissions-return-their-own-calculation
  (let [entered (promise) release (promise)
        calc (reuse/evaluator {:pure? true :inputs [[:x]]}
                              (fn [{:keys [x]}]
                                (when (= :slow x) (deliver entered true) (deref release 5000 false))
                                x))
        slow (future (calc {:x :slow}))]
    (try
      (is (deref entered 5000 false))
      (is (= :fast (calc {:x :fast})))
      (deliver release true)
      (is (= :slow (deref slow 5000 :timeout)))
      (is (= :fast (calc {:x :fast})))
      (finally (deliver release true)))))

(deftest inferred-clock-and-meter-inputs
  (is (= [[:position] [:beat] [:meter :beats-per-bar] [:meter :bars-per-phrase]
          [:elapsed-ms] [:params :level]]
         (ir/input-paths {:op :add :args [{:op :position :axis :x}
                                          {:op :phrase :clock :absolute}
                                          {:op :bar :clock :absolute}
                                          {:op :time} {:op :param :key :level}]}))))

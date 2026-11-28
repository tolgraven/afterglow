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

(deftest shared-outputs-retain-the-returned-arrays-without-copying
  (let [calls (atom 0)
        calc (reuse/evaluator {:pure? true :inputs [[:v]] :max-values 12 :shared-outputs? true}
                              (fn [{:keys [v]}] (swap! calls inc)
                                {:outputs {:red {:values (double-array [v 0.5])}}}))
        miss (calc {:v 0.25})
        hit (calc {:v 0.25})]
    (testing "a hit returns the value the miss returned, arrays included"
      (is (identical? miss hit))
      (is (identical? (get-in miss [:outputs :red :values]) (get-in hit [:outputs :red :values])))
      (is (= [0.25 0.5] (vec (get-in hit [:outputs :red :values]))))
      (is (= 1 @calls)))
    (testing "changed inputs evaluate again and replace the retained value"
      (let [next-value (calc {:v 0.75})]
        (is (not (identical? miss next-value)))
        (is (identical? next-value (calc {:v 0.75})))
        (is (= [0.75 0.5] (vec (get-in next-value [:outputs :red :values]))))
        (is (= 2 @calls))))
    (testing "shared array elements count against bytes, not :max-values"
      (let [long-array (reuse/evaluator {:pure? true :inputs [[:v]] :max-values 12 :shared-outputs? true}
                                        (fn [_] (swap! calls inc) {:values (double-array 16)}))]
        (is (identical? (long-array {:v 1}) (long-array {:v 1})))
        (is (= 3 @calls)))
      (let [big (reuse/evaluator {:pure? true :inputs [[:v]] :max-values 12 :shared-outputs? true
                                  :max-shared-bytes 127}
                                 (fn [_] (swap! calls inc) {:values (double-array 16)}))]
        (is (not (identical? (big {:v 1}) (big {:v 1}))))
        (is (= 5 @calls))))
    (testing "the default still gives each caller private arrays"
      (let [private (reuse/evaluator {:pure? true :inputs [[:v]]}
                                     (fn [_] {:values (double-array [1.0])}))
            a (private {:v 1}) b (private {:v 1})]
        (is (not (identical? (:values a) (:values b))))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (reuse/evaluator {:pure? true :inputs [] :shared-outputs? :yes} identity)))
    (is (thrown? clojure.lang.ExceptionInfo
                 (reuse/evaluator {:pure? true :inputs [] :shared-outputs? true :max-shared-bytes 0} identity)))))

(defn- rgbw-group
  "A typed batch evaluation of `n` pixels: a spatial colour and a white field."
  [n]
  (let [x {:op :position :axis :x}
        plan (ir/compile-batch {:color {:op :vec3 :args [{:op :multiply :args [{:op :param :key :level}
                                                                                {:op :sin :args [x]}]}
                                                         {:op :const :value 0.2} x]}
                                :white {:op :param :key :level}})
        positions (double-array (mapcat (fn [i] [(* 1.0e-4 i) 0.0 0.0]) (range n)))]
    (fn [inputs] (ir/evaluate-batch plan inputs positions))))

(deftest shared-batch-outputs-are-retained-above-sixty-five-thousand-elements
  ;; tolgraven/tolglow#875: 20,000 RGBW targets return 80,000 elements.
  (doseq [n [20000 40000]]
    (let [calls (atom 0)
          group (rgbw-group n)
          calc (reuse/evaluator {:pure? true :inputs [[:params :level]] :shared-outputs? true}
                                (fn [inputs] (swap! calls inc) (group inputs)))
          miss (calc {:params {:level 0.5}})
          hit (calc {:params {:level 0.5}})]
      (is (= (* 4 n) (+ (alength ^doubles (get-in miss [:outputs :color :values]))
                        (alength ^doubles (get-in miss [:outputs :white :values])))))
      (is (identical? (get-in miss [:outputs :color :values]) (get-in hit [:outputs :color :values])) (str n))
      (is (identical? (get-in miss [:outputs :white :values]) (get-in hit [:outputs :white :values])))
      (is (= 1 @calls) (str n " targets evaluate once"))
      (is (not (identical? miss (calc {:params {:level 0.25}}))))
      (is (= 2 @calls)))))

(deftest the-shared-byte-bound-is-exact-and-other-bounds-are-unchanged
  (let [bytes (* 8 (+ (* 3 1000) 1000))
        run (fn [declaration]
              (let [calls (atom 0)
                    group (rgbw-group 1000)
                    calc (reuse/evaluator (merge {:pure? true :inputs [[:params :level]]} declaration)
                                          (fn [inputs] (swap! calls inc) (group inputs)))
                    a (calc {:params {:level 0.5}}) b (calc {:params {:level 0.5}})]
                (is (java.util.Arrays/equals ^doubles (get-in a [:outputs :color :values])
                                             ^doubles (get-in b [:outputs :color :values])))
                @calls))]
    (testing "outputs up to :max-shared-bytes are retained, larger ones are not"
      (is (= 1 (run {:shared-outputs? true :max-shared-bytes bytes})))
      (is (= 2 (run {:shared-outputs? true :max-shared-bytes (dec bytes)}))))
    (testing "the default bound admits 8 MiB of float64 and no more"
      (is (= (* 8 1024 1024) reuse/default-max-shared-bytes (* 8 4 262144)))
      (doseq [[n retained?] [[(* 4 262144) true] [(inc (* 4 262144)) false]]]
        (let [calls (atom 0)
              calc (reuse/evaluator {:pure? true :inputs [[:v]] :shared-outputs? true}
                                    (fn [_] (swap! calls inc) {:values (double-array n)}))]
          (calc {:v 1}) (calc {:v 1})
          (is (= (if retained? 1 2) @calls) (str n " float64 elements under the default"))))))
  (testing "array bytes follow the element type"
    (doseq [[make n] [[float-array 16] [int-array 16] [long-array 8] [byte-array 64]
                      [short-array 32] [char-array 32] [boolean-array 64]]
            [length retained?] [[n true] [(inc n) false]]]
      (let [calls (atom 0)
            calc (reuse/evaluator {:pure? true :inputs [[:v]] :shared-outputs? true :max-shared-bytes 64}
                                  (fn [_] (swap! calls inc) {:values (make length)}))
            a (calc {:v 1}) b (calc {:v 1})]
        (is (= (if retained? 1 2) @calls) (str (class (:values a)) " of " length))
        (is (= retained? (identical? (:values a) (:values b)))))))
  (testing "copied outputs keep the 65,536-element bound"
    (doseq [[n retained?] [[65534 true] [65535 false]]]
      (let [calls (atom 0)
            calc (reuse/evaluator {:pure? true :inputs [[:v]]}
                                  (fn [_] (swap! calls inc) {:values (double-array n)}))]
        (calc {:v 1}) (calc {:v 1})
        (is (= (if retained? 1 2) @calls) (str n " copied elements")))))
  (testing "inputs keep the 65,536-node bound with shared outputs"
    (doseq [[n retained?] [[65534 true] [65536 false]]]
      (let [calls (atom 0)
            values (vec (repeat n 0.5))
            calc (reuse/evaluator {:pure? true :inputs [[:v]] :shared-outputs? true}
                                  (fn [_] (swap! calls inc) {:values (double-array 4)}))]
        (calc {:v values}) (calc {:v values})
        (is (= (if retained? 1 2) @calls) (str n " input elements"))))))

(deftest shared-outputs-reach-concurrent-readers-unchanged
  (let [calls (atom 0)
        calc (reuse/evaluator {:pure? true :inputs [[:beat]] :shared-outputs? true}
                              (fn [{:keys [beat]}] (swap! calls inc)
                                {:values (double-array (repeat 1024 (double beat)))}))
        retained (calc {:beat 2.0})
        pool (java.util.concurrent.Executors/newFixedThreadPool 4)]
    (try
      (let [results (mapv deref (.invokeAll pool (vec (repeat 64 (fn [] (calc {:beat 2.0})))) ))]
        (is (every? #(identical? retained %) results))
        (is (every? #(== 2.0 %) (:values retained)))
        (is (= 1 @calls)))
      (finally (.shutdownNow pool)))))

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

(deftest clearing-a-binding-drops-its-retained-value
  (let [calls (atom 0)
        group (rgbw-group 20000)
        calc (reuse/evaluator {:pure? true :inputs [[:params :level]] :shared-outputs? true}
                              (fn [inputs] (swap! calls inc) (group inputs)))
        context {:params {:level 0.5}}]
    (is (not (reuse/retains? calc)))
    (let [first-value (calc context)]
      (is (reuse/retains? calc))
      (is (nil? (reuse/clear! calc)))
      (is (not (reuse/retains? calc)) "nothing holds the 80,000 elements any more")
      (testing "the binding stays usable and retains again"
        (let [again (calc context)]
          (is (= 2 @calls))
          (is (not (identical? first-value again)))
          (is (java.util.Arrays/equals ^doubles (get-in first-value [:outputs :color :values])
                                       ^doubles (get-in again [:outputs :color :values])))
          (is (identical? again (calc context)))
          (is (= 2 @calls))))))
  (testing "a step clears like its evaluator, and other functions are ignored"
    (let [step (reuse/step {:pure? true :inputs [[:v]]} (fn [{:keys [v]}] {:assignments [v]}))]
      (step {:v 1 :assignments []})
      (is (reuse/retains? step))
      (reuse/clear! step)
      (is (not (reuse/retains? step))))
    (is (nil? (reuse/clear! identity)))
    (is (not (reuse/retains? identity)))))

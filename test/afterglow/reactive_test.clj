(ns afterglow.reactive-test
  (:require [clojure.edn :as edn]
            [clojure.test :refer [deftest is testing]]
            [afterglow.reactive :as reactive]
            [afterglow.reactive.clock :as clock]
            [afterglow.reactive.registry :as registry])
  (:import [java.util.concurrent CountDownLatch Executors TimeUnit Callable]))

(defn value-sub [{:keys [db]} _] (:value @db))
(def value-definition {:id ::value :kind :sub :implementation {:type :var :symbol "afterglow.reactive-test/value-sub"}})
(defn- error-type [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo error (:type (ex-data error)))))

(deftest ratoms-preserve-ordinary-atom-operations
  (let [system (reactive/create-system {}) cell (reactive/ratom system ::level 1) calls (atom [])]
    (is (identical? cell (reactive/ratom system ::level 999)))
    (add-watch cell ::changes (fn [key _ old new] (swap! calls conj [key old new])))
    (is (= 2 (reset! cell 2)))
    (is (= 2 @cell))
    (is (= 5 (swap! cell + 3)))
    (is (= [5 9] (swap-vals! cell + 4)))
    (is (= [9 3] (reset-vals! cell 3)))
    (is (compare-and-set! cell @cell 4))
    (is (false? (compare-and-set! cell 3 7)))
    (set-validator! cell #(<= 0 % 10))
    (is (= ::reactive/invalid-value (error-type #(reset! cell 99))))
    (is (= 4 @cell))
    (is (= [[::changes 1 2] [::changes 2 5] [::changes 5 9] [::changes 9 3] [::changes 3 4]] @calls))
    (remove-watch cell ::changes)
    (reset! cell 5)
    (is (= 5 (count @calls)))))

(deftest dependency-tracking-prunes-unchanged-derived-values
  (let [system (reactive/create-system {:value 2 :other 0}) calls (atom {:value 0 :double 0})]
    (reactive/reg-sub! system ::value (fn [{:keys [db]} _] (swap! calls update :value inc) (:value @db)))
    (reactive/reg-sub! system ::double (fn [{:keys [subscribe]} _] (swap! calls update :double inc) (* 2 @(subscribe [::value]))))
    (let [signal (reactive/subscribe system [::double])]
      (is (= 4 @signal))
      (is (identical? signal (reactive/subscribe system [::double])))
      (reactive/publish! system {:value 2 :other 1})
      (is (= {:value 2 :double 1} @calls))
      (reactive/publish! system {:value 3 :other 1})
      (is (= 6 @signal))
      (is (= {:value 3 :double 2} @calls))
      (reactive/publish! system {:value 3 :other 1})
      (is (= {:value 3 :double 2} @calls))
      ;; Replacing a handler reruns it, but equality still suppresses descendants.
      (reactive/reg-sub! system ::value value-sub)
      (reactive/publish! system)
      (is (= 2 (:double @calls))))))

(deftest form-two-subscriptions-create-their-inner-function-once
  (let [system (reactive/create-system {:value 3}) outer (atom 0) inner (atom 0)]
    (reactive/reg-sub! system ::value value-sub)
    (reactive/reg-sub! system ::scaled
                       (fn [{:keys [subscribe]} [_ factor]]
                         (swap! outer inc)
                         (let [value (subscribe [::value])]
                           (fn [] (swap! inner inc) (* factor @value)))))
    (let [signal (reactive/subscribe system [::scaled 4])]
      (is (= 12 @signal))
      (reactive/publish! system {:value 5})
      (is (= 20 @signal))
      (reactive/publish! system {:value 5})
      (is (= [1 2] [@outer @inner]))
      (is (= 10 @(reactive/subscribe system [::scaled 2])))
      (is (= [2 3] [@outer @inner])))))

(deftest dynamic-dependencies-detach-unused-sources
  (let [system (reactive/create-system {}) choose (reactive/ratom system ::choose true)
        left (reactive/ratom system ::left 1) right (reactive/ratom system ::right 10)
        calls (atom 0) result (reactive/reaction system ::choice #(do (swap! calls inc) (if @choose @left @right)))]
    (is (= 1 @result))
    (reset! right 20) (reactive/publish! system)
    (is (= 1 @calls))
    (reset! choose false) (reactive/publish! system)
    (is (= 20 @result))
    (reset! left 2) (reactive/publish! system)
    (is (= 2 @calls))
    (reset! right 30) (reactive/publish! system)
    (is (= [30 3] [@result @calls]))))

(deftest a-batch-freezes-sources-even-when-a-handler-writes-a-ratom
  (let [system (reactive/create-system {}) cell (reactive/ratom system ::value 1)
        writer (reactive/reaction system ::writer #(let [before @cell] (when (= before 2) (reset! cell 3)) [before @cell]))
        reader (reactive/reaction system ::reader #(identity @cell))]
    (is (= [1 1] @writer)) (is (= 1 @reader))
    (reset! cell 2)
    (reactive/publish! system)
    (is (= 3 @cell) "source writes retain immediate atom semantics")
    (is (= [[2 2] 2] [@writer @reader]) "every derivation reads the same captured value")
    (reactive/publish! system)
    (is (= [[3 3] 3] [@writer @reader]))))

(deftest real-threads-cannot-mix-a-publish-snapshot
  (let [system (reactive/create-system {}) cell (reactive/ratom system ::value 1)
        entered (CountDownLatch. 1) release (CountDownLatch. 1) attempting (CountDownLatch. 1)
        pool (Executors/newFixedThreadPool 2)
        signal (reactive/reaction system ::pair
                                  #(let [a @cell]
                                     (when (= a 2) (.countDown entered) (.await release 5 TimeUnit/SECONDS))
                                     [a @cell]))]
    (try
      (is (= [1 1] @signal)) (reset! cell 2)
      (let [published (.submit pool ^Callable (fn [] (reactive/publish! system)))
            _ (is (.await entered 5 TimeUnit/SECONDS))
            updated (.submit pool ^Callable (fn [] (.countDown attempting) (reset! cell 3)))]
        (is (.await attempting 5 TimeUnit/SECONDS))
        (.countDown release)
        (.get published 5 TimeUnit/SECONDS) (.get updated 5 TimeUnit/SECONDS)
        (is (= [2 2] @signal))
        (is (= 3 @cell))
        (reactive/publish! system)
        (is (= [3 3] @signal)))
      (finally (.countDown release) (.shutdownNow pool)))))

(deftest swap-functions-run-once-not-in-a-retry-loop
  (let [system (reactive/create-system {}) cell (reactive/ratom system ::count 0)
        calls (atom 0) pool (Executors/newFixedThreadPool 4)]
    (try
      (let [jobs (doall (for [_ (range 4)] (.submit pool ^Callable
                                                  (fn [] (dotimes [_ 100] (swap! cell #(do (swap! calls inc) (inc %))))))))]
        (doseq [job jobs] (.get job 5 TimeUnit/SECONDS))
        (is (= [400 400] [@cell @calls])))
      (finally (.shutdownNow pool)))))

(deftest cycles-fail-without-publishing-a-partial-cache
  (let [system (reactive/create-system {})]
    (reactive/reg-sub! system ::a (fn [{:keys [subscribe]} _] @(subscribe [::b])))
    (reactive/reg-sub! system ::b (fn [{:keys [subscribe]} _] @(subscribe [::a])))
    (is (= ::reactive/cycle (error-type #(reactive/subscribe system [::a]))))
    (reactive/reg-sub! system ::b (fn [_ _] 7))
    (is (= 7 @(reactive/subscribe system [::a])))))

(deftest watchers-queue-actions-only-when-their-selected-value-changes
  (let [system (doto (reactive/create-system {:transport {:beat 1.1}}) clock/register!)]
    (reactive/reg-fx! system ::launch (fn [_ new old] {:op :cue/launch :cue-id ::beat :params {:new new :old old}}))
    (reactive/watch! system ::beat-action [:clock/beat] ::launch)
    (reactive/publish! system)
    (is (= [{:op :cue/launch :cue-id ::beat :params {:new 1 :old nil}}] (reactive/drain-actions! system)))
    (reactive/publish! system {:transport {:beat 1.9}})
    (is (= [] (reactive/drain-actions! system)))
    (reactive/publish! system {:transport {:beat 2.1}})
    (is (= [{:op :cue/launch :cue-id ::beat :params {:new 2 :old 1}}] (reactive/drain-actions! system)))
    (is (= [] (reactive/drain-actions! system)))
    (reactive/unwatch! system ::beat-action)
    (reactive/publish! system {:transport {:beat 3.1}})
    (is (= [] (reactive/drain-actions! system)))))

(deftest failed-batches-do-not-publish-values-actions-or-watcher-comparisons
  (let [system (reactive/create-system {:value 1}) fail? (atom false)]
    (reactive/reg-sub! system ::value value-sub)
    (reactive/reg-fx! system ::first (fn [_ value _] {:op :master/set :value value}))
    (reactive/reg-fx! system ::last (fn [_ _ _] (when @fail? (throw (ex-info "handler failed" {})))))
    (reactive/watch! system ::first [::value] ::first)
    (reactive/watch! system ::last [::value] ::last)
    (reactive/publish! system) (reactive/drain-actions! system)
    (reset! fail? true)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"handler failed" (reactive/publish! system {:value 2})))
    (is (= [] (reactive/drain-actions! system)))
    (is (= 1 @(reactive/subscribe system [::value])))
    (reset! fail? false)
    (reactive/publish! system)
    (is (= [{:op :master/set :value 2}] (reactive/drain-actions! system)))
    (is (= 2 @(reactive/subscribe system [::value])))))

(deftest watch-callbacks-observe-an-already-committed-dag
  (let [system (reactive/create-system {:value 1}) observations (atom [])]
    (reactive/reg-sub! system ::value value-sub)
    (reactive/reg-sub! system ::double (fn [{:keys [subscribe]} _] (* 2 @(subscribe [::value]))))
    (let [a (reactive/subscribe system [::value]) b (reactive/subscribe system [::double])]
      (add-watch a ::observer (fn [_ _ old new] (swap! observations conj [old new @b])))
      (reactive/publish! system {:value 2})
      (is (= [[1 2 4]] @observations)))))

(deftest portable-repl-source-captures-values-once-and-restores
  (let [system (reactive/create-system {:value 4}) evaluated (atom 0)]
    (reactive/reg-sub system ::scaled {factor (do (swap! evaluated inc) 3)}
                      (fn [{:keys [db]} _] (* factor (:value @db))))
    (is (= 1 @evaluated))
    (is (= 12 @(reactive/subscribe system [::scaled])))
    (let [saved (edn/read-string (pr-str (reactive/export-registry system)))
          restored (reactive/create-system {:value 5})]
      (is (= 3 (get-in saved [:registrations 0 :implementation :bindings "factor"])))
      (is (= ::registry/untrusted-source (error-type #(reactive/restore! restored saved))))
      (reactive/restore! restored saved {:trusted-source? true})
      (is (= 15 @(reactive/subscribe restored [::scaled]))))))

(deftest saving-a-show-preserves-ratoms-queued-actions-and-last-handled-beat
  (let [system (doto (reactive/create-system {:transport {:beat 3.25}}) clock/register!)
        level (reactive/ratom system ::level 0.5)]
    (reactive/reg-sub system ::cell-value {}
                      (fn [{:keys [source]} _] @(source ::level)))
    (reactive/reg-fx system ::launch {cue-id ::red}
                     (fn [_ beat _] {:op :cue/launch :cue-id cue-id :params {:beat beat}}))
    (reactive/watch! system ::on-beat [:clock/beat] ::launch)
    (reactive/publish! system)
    (is (= 1 (count (reactive/drain-actions! system))))
    (reset! level 0.75)
    (reactive/queue-action! system {:op :param/set :instance-id "0:1" :param :level :value 0.4})
    (let [saved (edn/read-string (pr-str (reactive/export-registry system)))
          restored (reactive/create-system {:transport {:beat 3.8}})]
      (reactive/restore! restored saved {:trusted-source? true})
      (is (= 0.75 @(reactive/ratom restored ::level 0)))
      (is (= 0.75 @(reactive/subscribe restored [::cell-value])))
      (is (= [{:op :param/set :instance-id "0:1" :param :level :value 0.4}] (reactive/drain-actions! restored)))
      (reactive/publish! restored)
      (is (= [] (reactive/drain-actions! restored)) "same handled beat is not replayed on restore")
      (reactive/publish! restored {:transport {:beat 4.1}})
      (is (= [{:op :cue/launch :cue-id ::red :params {:beat 4}}] (reactive/drain-actions! restored))))))

(deftest registry-validation-is-data-only-and-rejects-unportable-or-unbound-inputs
  (let [calls (atom 0) source {:id ::value :kind :sub :implementation {:type :source :namespace "user" :form "(fn [_ _] #unsafe/tag 1)" :bindings {}}}]
    (binding [*data-readers* {'unsafe/tag (fn [x] (swap! calls inc) x)}]
      (is (thrown? clojure.lang.ExceptionInfo (registry/validate-registry {:registrations [source]}))))
    (is (= 0 @calls))
    (doseq [form ["#=(System/exit 0)" "(do (println :oops) (fn [_ _] 1))" "(fn [_ _] 1) (println :oops)"]]
      (is (thrown? clojure.lang.ExceptionInfo (registry/validate-registry {:registrations [(assoc-in source [:implementation :form] form)]})))))
  (let [system (reactive/create-system {})]
    (reactive/reg-sub! system ::opaque (fn [_ _] 1))
    (is (= ::reactive/unpersistable-handler (error-type #(reactive/export-registry system))))
    (is (= ::reactive/invalid-action (error-type #(reactive/queue-action! system {:op :cue/launch :epoch 3})))))
  (is (thrown? clojure.lang.ExceptionInfo
               (registry/validate-registry {:registrations [value-definition]
                                            :state {:cells {} :pending-actions []
                                                    :watchers [{:id ::bad :query [::missing] :effect-id ::missing :initialized? true :value 1}]}}))))

(deftest failed-restore-preserves-the-live-graph
  (let [system (reactive/create-system {:value 5})
        broken {:registrations [{:id ::bad :kind :sub :implementation {:type :source :namespace "user" :bindings {} :form "(fn [_ _] (throw (ex-info \"broken factory\" {})))"}}
                                 {:id ::fx :kind :fx :implementation {:type :source :namespace "user" :bindings {} :form "(fn [_ _ _] nil)"}}]
                :state {:cells {::extra 99} :pending-actions [] :watchers [{:id ::bad :query [::bad] :effect-id ::fx :initialized? true :value 2}]}}]
    (reactive/reg-sub! system ::value value-sub value-definition)
    (let [signal (reactive/subscribe system [::value])]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"broken factory" (reactive/restore! system broken {:trusted-source? true})))
      (is (identical? signal (reactive/subscribe system [::value])))
      (is (= 5 @signal))
      (is (= [value-definition] (:registrations (reactive/export-registry system)))))))

(deftest dispose-close-and-cross-system-ownership
  (let [system (reactive/create-system {:value 1}) other (reactive/create-system {})]
    (reactive/reg-sub! system ::value value-sub)
    (let [old (reactive/subscribe system [::value])]
      (reactive/dispose! old)
      (is (= ::reactive/disposed (error-type #(deref old))))
      (let [fresh (reactive/subscribe system [::value])]
        (is (not (identical? old fresh)))
        (is (= ::reactive/disposed (error-type #(deref old))))))
    (let [foreign (reactive/ratom other ::foreign 3)
          bad (reactive/reaction system ::bad #(deref foreign))]
      (is (= ::reactive/cross-system (error-type #(deref bad)))))
    (reactive/close! system)
    (is (= ::reactive/closed (error-type #(reactive/publish! system))))))

(deftest musical-clock-subscriptions-use-the-explicit-meter
  (let [system (doto (reactive/create-system {:transport {:beat 20.25 :meter {:beats-per-bar 3 :bars-per-phrase 2}}}) clock/register!)]
    (is (= [20 2 6 3 0.25]
           (mapv #(deref (reactive/subscribe system [%])) [:clock/beat :clock/beat-in-bar :clock/bar :clock/phrase :clock/phase])))
    (is (= 5 (count (:registrations (reactive/export-registry system)))))))

(deftest stale-handles-cannot-dispose-or-change-the-replacement
  (let [system (reactive/create-system {}) old (reactive/ratom system ::level 1)]
    (reactive/dispose! old)
    (let [fresh (reactive/ratom system ::level 2)]
      (is (= ::reactive/disposed (error-type #(reactive/dispose! old))))
      (is (= ::reactive/disposed (error-type #(add-watch old ::bad (fn [& _])))))
      (is (= ::reactive/disposed (error-type #(reset! old 3))))
      (is (= 2 @fresh)))
    (reactive/reg-sub! system ::value (fn [_ _] 4))
    (let [old (reactive/subscribe system [::value])]
      (reactive/dispose! old)
      (let [fresh (reactive/subscribe system [::value])]
        (is (= ::reactive/disposed (error-type #(reactive/dispose! old))))
        (is (= ::reactive/disposed (error-type #(remove-watch old ::bad))))
        (is (= 4 @fresh))))))

(deftest callbacks-cannot-remove-the-current-graph-during-evaluation
  (let [system (reactive/create-system {:value 1})]
    (reactive/reg-sub! system ::value value-sub)
    (reactive/reg-fx! system ::self-remove (fn [_ _ _] (reactive/unwatch! system ::watcher) nil))
    (reactive/watch! system ::watcher [::value] ::self-remove)
    (is (= ::reactive/mutation-during-evaluation (error-type #(reactive/publish! system))))
    (is (= [] (reactive/drain-actions! system)))
    ;; The failed attempt cannot leave a malformed partial watcher behind.
    (reactive/reg-fx! system ::self-remove (fn [_ value _] {:op :master/set :value value}))
    (reactive/publish! system)
    (is (= [{:op :master/set :value 1}] (reactive/drain-actions! system)))
    (reactive/publish! system)
    (is (= [] (reactive/drain-actions! system)))))

(deftest source-writes-during-restore-are-rejected-without-changing-the-live-db
  (let [system (reactive/create-system {:value 7})
        data {:registrations [{:id ::write :kind :sub :implementation {:type :source :namespace "user" :bindings {}
                                                                      :form "(fn [{:keys [db]} _] (reset! db {:value 99}) 1)"}}
                              {:id ::fx :kind :fx :implementation {:type :source :namespace "user" :bindings {} :form "(fn [_ _ _] nil)"}}]
              :state {:cells {} :pending-actions [] :watchers [{:id ::w :query [::write] :effect-id ::fx :initialized? true :value 1}]}}]
    (reactive/reg-sub! system ::value value-sub value-definition)
    (let [old (reactive/subscribe system [::value])]
      (is (= ::reactive/restore-mutation (error-type #(reactive/restore! system data {:trusted-source? true}))))
      (is (= {:value 7} @(reactive/db-signal system)))
      (is (identical? old (reactive/subscribe system [::value])))
      (is (= 7 @old)))))

(deftest traced-publication-reports-real-deliveries-and-keeps-arguments-private
  (let [system (reactive/create-system {:value 0})
        hits (atom 0)]
    (reactive/reg-sub! system ::floor (fn [{:keys [db]} _] (quot (:value @db) 2)))
    (reactive/reg-fx! system ::count (fn [_ _ _] (swap! hits inc) nil))
    (reactive/watch! system ::watch [::floor "private query argument"] ::count)
    (let [trace #(:delivery-trace (reactive/publish-traced! system {:value %}))
          initial (trace 2) same (trace 3) changed (trace 4)
          calls #(filter (comp #{:reactive/dispatch} :type) (:events %))]
      (is (= [::watch] (:subscribers (first (calls initial)))))
      (is (= {:kind :subscription :id ::floor} (:emitter (first (calls changed)))))
      (is (= ::count (get-in (first (calls changed)) [:data :registration-id])))
      (is (empty? (calls same)))
      (is (some #(and (= :reactive/read (:type %)) (= [::floor] (:subscribers %))) (:events same)))
      (is (not (.contains (pr-str changed) "private query argument")))
      (is (= 0 (:skipped changed)))
      (is (= 2 @hits))
      (is (not (contains? (reactive/publish! system {:value 7}) :delivery-trace))))))

(ns afterglow.reactive-test
  (:require [clojure.edn :as edn]
            [clojure.test :refer [deftest is testing]]
            [afterglow.reactive :as reactive]
            [afterglow.reactive.clock :as clock]
            [afterglow.reactive.registry :as registry])
  (:import [java.util.concurrent Callable CountDownLatch Executors LinkedBlockingQueue TimeUnit]))

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
        _ (reactive/reg-sub! system ::reader (fn [_ _] @cell))
        {:keys [signal close!]} (reactive/acquire! system [::reader] (constantly nil))
        bindings {:source [:source ::value] :derived [:subscription [::reader]]}]
    (try
      (is (= [1 1] @writer)) (is (= 1 @signal))
      (reset! cell 2)
      (is (= {:source 2 :derived 2} (:inputs (reactive/publish! system {} bindings))))
      (is (= 3 @cell) "source writes retain immediate atom semantics")
      (is (= [[2 2] 2] [@writer @signal]) "every derivation reads the same captured value")
      (is (= {:source 3 :derived 3} (:inputs (reactive/publish! system {} bindings))))
      (is (= [[3 3] 3] [@writer @signal]))
      (finally (close!) (reactive/close! system)))))

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

(deftest a-failed-effect-cannot-discard-sibling-actions-or-enqueue-a-partial-result
  (let [reported (atom [])
        system (reactive/create-system {:value 1} {:on-fault! (fn [entry _] (swap! reported conj entry))})]
    (reactive/reg-sub! system ::value value-sub)
    (reactive/reg-fx! system ::broken (fn [{:keys [queue-action!]} _ _]
                                        (queue-action! {:op :partial})
                                        (throw (ex-info "handler failed" {}))))
    (reactive/reg-fx! system ::good (fn [_ value _] {:op :master/set :value value}))
    (reactive/watch! system ::a [::value] ::good)
    (reactive/watch! system ::b [::value] ::broken)
    (reactive/watch! system ::c [::value] ::good)
    (let [batch (reactive/publish! system {:value 2})]
      (is (= [{:op :master/set :value 2} {:op :master/set :value 2}] (reactive/drain-actions! system)))
      (is (= @reported (:faults batch) (reactive/faults system)))
      (is (= [[:effect-handler ::broken "handler failed"]]
             (mapv (juxt :stage :id :message) (:faults batch))))
      (is (seq (:stacktrace (first (:faults batch))))))
    (reactive/publish! system)
    (is (= 1 (count @reported)))
    (is (= [] (reactive/drain-actions! system)))))

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
    (is (= [:effect-handler ::self-remove]
           ((juxt :stage :id) (first (:faults (reactive/publish! system))))))
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

(deftest leased-dependency-trees-stop-producing-after-last-consumer
  (let [system (reactive/create-system {})
        input (atom {:x 1}) calls (atom [0 0]) changes (atom [])]
    (reactive/reg-ref! system ::input input :x)
    (reactive/reg-sub! system ::x (fn [{:keys [cofx]} _] (swap! calls update 0 inc) (cofx ::input)))
    (reactive/reg-sub! system ::greater (fn [{:keys [subscribe]} _]
                                         (swap! calls update 1 inc) (> @(subscribe [::x]) 1)))
    (is (empty? (.getWatches input)))
    (let [a (reactive/acquire! system [::greater] #(swap! changes conj [:a %]))
          b (reactive/acquire! system [::greater] #(swap! changes conj [:b %]))]
      (is (= false (:value a) (:value b)))
      (is (= #{[::x] [::greater]} (reactive/demanded-queries system #{::greater ::x})))
      (is (= [1 1] @calls))
      (is (= 1 (count (.getWatches input))))
      (swap! input assoc :y 2)
      (reactive/publish! system)
      (is (= [1 1] @calls))
      ((:close! a))
      (swap! input assoc :x 3)
      (reactive/publish! system)
      (is (= [[:b true]] @changes))
      (swap! input assoc :x 5)
      (reactive/publish! system)
      (is (= [3 3] @calls))
      (is (= [[:b true]] @changes))
      ((:close! a)) ((:close! b))
      (is (empty? (.getWatches input)))
      (is (false? (reactive/demanded? system #{::x ::greater})))
      (swap! input assoc :x -1)
      (reactive/publish! system)
      (is (= [3 3] @calls))
      (let [again (reactive/acquire! system [::greater] identity)]
        (is (false? (:value again))) ((:close! again))))
    (reactive/close! system)))

(deftest form-two-reacquires-sources-when-a-branch-returns
  (let [system (reactive/create-system {:read? true}) ext (atom 10)]
    (reactive/reg-ref! system ::input ext)
    (reactive/reg-sub! system ::n (fn [{:keys [cofx]} _] (cofx ::input)))
    (reactive/reg-sub! system ::switch
                       (fn [{:keys [db subscribe]} _]
                         (let [n (subscribe [::n])]
                           #(when (:read? @db) @n))))
    (let [lease (reactive/acquire! system [::switch] identity)]
      (is (= 10 (:value lease)))
      (reactive/publish! system {:read? false})
      (is (empty? (.getWatches ext)))
      (is (nil? @(:signal lease)))
      (reset! ext 25)
      (reactive/publish! system {:read? true})
      (is (= 25 @(:signal lease)))
      (is (= 1 (count (.getWatches ext))))
      ((:close! lease))
      (is (empty? (.getWatches ext))))))

(deftest schema-failure-is-contained-and-recovers-on-next-valid-input
  (let [system (reactive/create-system {:value 1} {:on-fault! (fn [_ _])}) events (atom [])]
    (reactive/reg-sub! system ::positive value-sub {:validate pos-int? :fallback 7 :owner {:cue-id :red}})
    (reactive/reg-sub! system ::default value-sub {:validate pos-int? :on-error :fallback :fallback 5})
    (let [a (reactive/acquire! system [::positive] #(swap! events conj %))
          b (reactive/acquire! system [::default] identity)]
      (reactive/publish! system {:value -1})
      (is (= [1 5] [@(:signal a) @(:signal b)]))
      (is (= [] @events))
      (is (= #{::positive ::default} (into #{} (map :id) (reactive/faults system))))
      (is (= :red (:cue-id (first (filter #(= ::positive (:id %)) (reactive/faults system))))))
      (reactive/publish! system {:value 3})
      (is (= [3] @events))
      ((:close! b)) ((:close! a)))
    (reactive/close! system)))

(deftest fallback-only-subscriptions-deliver-only-available-values
  (doseq [[options expected] [[{:validate number?} []]
                              [{:validate #(or (nil? %) (number? %)) :fallback nil} [nil]]]]
    (let [system (reactive/create-system {:value 1} {:on-fault! (fn [_ _])})
          observed (atom [])
          effected (atom [])]
      (try
        (reactive/reg-sub! system ::value value-sub (assoc options :on-error :fallback))
        (reactive/reg-fx! system ::record (fn [_ v _] (swap! effected conj v) nil))
        (reactive/watch! system ::watch [::value] ::record)
        (let [lease (reactive/acquire! system [::value] #(swap! observed conj %))]
          (is (= 1 (:value lease)))
          (reactive/publish! system)
          (reactive/publish! system {:value :invalid})
          (is (= expected @observed))
          (is (= (into [1] expected) @effected))
          (reactive/publish! system {:value 2})
          (is (= (conj expected 2) @observed))
          (is (= (into [1] (conj expected 2)) @effected)))
        (finally (reactive/close! system))))))

(deftest first-invalid-value-without-fallback-does-not-trigger-downstream-effects
  (let [system (reactive/create-system {:value -1} {:on-fault! (fn [_ _])}) delivered (atom [])]
    (reactive/reg-sub! system ::positive value-sub {:validate pos-int?})
    (reactive/reg-sub! system ::times-two (fn [{:keys [subscribe]} _] (* 2 @(subscribe [::positive]))))
    (reactive/reg-fx! system ::send (fn [_ v _] (swap! delivered conj v) nil))
    (reactive/watch! system ::observe [::times-two] ::send)
    (reactive/publish! system)
    (is (empty? @delivered))
    (is (= [::positive] (mapv :id (reactive/faults system))))
    (reactive/publish! system {:value 4})
    (is (= [8] @delivered))
    (reactive/unwatch! system ::observe)
    (is (false? (reactive/demanded? system #{::positive})))))

(deftest explicitly-invalidated-and-per-frame-coeffects-have-independent-cadences
  (let [sys (reactive/create-system {:value 1}) reads (atom 0) frames (atom 0)]
    (reactive/reg-cofx! sys ::sample {:sample (fn [_] (swap! reads inc))})
    (reactive/reg-cofx! sys ::frame {:mode :frame :sample (fn [_] (swap! frames inc))})
    (reactive/reg-sub! sys ::s (fn [{:keys [cofx]} _] [(cofx ::sample) (cofx ::sample)]))
    (reactive/reg-sub! sys ::f (fn [{:keys [cofx]} _] (cofx ::frame)))
    (let [slow (reactive/acquire! sys [::s] identity) fast (reactive/acquire! sys [::f] identity)]
      (is (= [1 1] (:value slow)))
      (is (= 1 (:value fast)))
      (reactive/publish! sys {:value 2})
      (is (= [1 2] [@reads @frames]))
      (is (true? (reactive/invalidate! sys [::s])))
      (reactive/publish! sys {:value 3})
      (is (= [2 2] @(:signal slow)))
      ((:close! slow)) ((:close! fast))
      (reactive/publish! sys)
      (is (= [2 3] [@reads @frames])))))

(deftest background-sampling-respects-musical-boundaries-and-stale-leases
  (let [sys (reactive/create-system {:transport {:beat 0}}) seen (atom [])
        started (CountDownLatch. 1) release (CountDownLatch. 1) ended (CountDownLatch. 1)
        cycles (java.util.concurrent.LinkedBlockingQueue.)]
    (try
      (reactive/reg-cofx! sys ::remote
                          {:mode :background :interval {:beats 1/2} :initial -1
                           :sample (fn [db]
                                     (.countDown started)
                                     (try (.await release 3 TimeUnit/SECONDS)
                                          (catch InterruptedException _ (.await release 3 TimeUnit/SECONDS)))
                                     (let [beat (get-in db [:transport :beat])]
                                       (.put cycles beat)
                                       (.countDown ended)
                                       beat))})
      (reactive/reg-sub! sys ::r (fn [{:keys [cofx]} _] (cofx ::remote)))
      (let [old (reactive/acquire! sys [::r] #(swap! seen conj %))]
        (is (= -1 (:value old)))
        (is (.await started 3 TimeUnit/SECONDS))
        (reactive/publish! sys {:transport {:beat 1/4}})
        ((:close! old))
        (.countDown release)
        (is (.await ended 3 TimeUnit/SECONDS))
        (is (= 0 (.poll cycles 3 TimeUnit/SECONDS)))
        (let [new (reactive/acquire! sys [::r] #(swap! seen conj %))]
          (is (= 1/4 (.poll cycles 3 TimeUnit/SECONDS)))
          ;; A finished sample is delivered at a publication, never by the IO worker.
          (is (some true? (for [_ (range 100) :while (empty? @seen)]
                            (do (Thread/sleep 1) (reactive/publish! sys) (= [1/4] @seen)))))
          (reactive/publish! sys {:transport {:beat 0.49}})
          (is (nil? (.poll cycles 20 TimeUnit/MILLISECONDS)))
          (reactive/publish! sys {:transport {:beat 1/2}})
          (is (= 1/2 (.poll cycles 3 TimeUnit/SECONDS)))
          ((:close! new))))
      (finally (.countDown release) (reactive/close! sys)))))

(deftest wall-paced-coeffects-sample-without-an-owner-publication-and-stop-on-release
  (let [sys (reactive/create-system {}) calls (atom 0) samples (CountDownLatch. 2)]
    (try
      (reactive/reg-cofx! sys ::remote
                          {:mode :background :interval {:fps 50} :initial 0
                           :sample (fn [_] (let [n (swap! calls inc)] (.countDown samples) n))})
      (reactive/reg-sub! sys ::r (fn [{:keys [cofx]} _] (cofx ::remote)))
      (let [lease (reactive/acquire! sys [::r] identity)]
        (is (.await samples 3 TimeUnit/SECONDS))
        (is (some true? (for [_ (range 100)]
                          (do (reactive/publish! sys) (Thread/sleep 1) (<= 2 @(:signal lease))))))
        ((:close! lease))
        (is (empty? (:cofx-snapshot @(:state sys))) "Released producers must drop their last sampled values.")
        (let [n @calls] (Thread/sleep 80) (is (= n @calls))))
      (finally (reactive/close! sys)))))

(deftest frame-paced-coeffects-follow-committed-frames-and-stop-with-the-last-lease
  (let [model {:show-id :show :epoch 0 :revision 0 :level :steady
               :transport {:beat 8 :playing? false}}
        sys (reactive/create-system model)
        samples (LinkedBlockingQueue.) changes (LinkedBlockingQueue.)
        raw-values (LinkedBlockingQueue.)
        release (CountDownLatch. 1) interrupted (CountDownLatch. 1)
        publish-frame! (fn [db expected]
                         (is (= expected
                                (some (fn [_]
                                        (reactive/publish! sys db)
                                        (.poll samples 20 TimeUnit/MILLISECONDS))
                                      (range 150)))))
        expect-value! (fn [^LinkedBlockingQueue received expected]
                        (is (= expected
                               (some (fn [_]
                                       (reactive/publish! sys)
                                       (.poll received 20 TimeUnit/MILLISECONDS))
                                     (range 150)))))
        expect-no-sample! #(is (nil? (.poll samples 20 TimeUnit/MILLISECONDS)))]
    (try
      (reactive/reg-cofx! sys ::remote
                          {:mode :background :interval {:frames 2} :initial [nil :waiting]
                           :sample (fn [{:keys [epoch frame-number level block?]}]
                                     (.offer samples [epoch frame-number])
                                     (when block?
                                       (try (.await release)
                                            (catch InterruptedException e
                                              (.countDown interrupted)
                                              (throw e))))
                                     [frame-number level])})
      (reactive/reg-sub! sys ::r (fn [{:keys [cofx]} _] (cofx ::remote)))
      (reactive/reg-sub! sys ::level (fn [{:keys [subscribe]} _] (second @(subscribe [::r]))))
      (reactive/publish! sys (assoc model :frame-number 0))
      (expect-no-sample!)
      (reactive/publish! sys model)
      (let [a (reactive/acquire! sys [::r] #(.offer raw-values %))
            b (reactive/acquire! sys [::level] #(.offer changes %))]
        (is (= [nil :waiting] (:value a)))
        (is (= :waiting (:value b)))
        (expect-no-sample!)
        (publish-frame! (assoc model :frame-number 0) [0 0])
        (expect-value! raw-values [0 :steady])
        (expect-value! changes :steady)
        (reactive/publish! sys (assoc model :frame-number 0 :revision 1 :time-ms 10000))
        (reactive/publish! sys (assoc-in (assoc model :frame-number 1) [:transport :beat] 40))
        (expect-no-sample!)
        (publish-frame! (assoc model :frame-number 2) [0 2])
        (expect-value! raw-values [2 :steady])
        (is (.isEmpty changes) "A distinct upstream sample can leave the consumer's selection unchanged.")
        ((:close! a))
        (publish-frame! (assoc model :frame-number 9 :level :updated) [0 9])
        (expect-value! changes :updated)
        (is (.isEmpty raw-values))
        (expect-no-sample!)
        (publish-frame! (assoc model :epoch 1 :frame-number 8 :block? true) [1 8])
        (reactive/publish! sys (assoc model :epoch 1 :frame-number 10))
        (expect-no-sample!)
        ((:close! b))
        (is (.await interrupted 3 TimeUnit/SECONDS))
        (is (false? (reactive/demanded? sys #{::r})))
        (reactive/publish! sys (assoc model :epoch 1 :frame-number 12))
        (expect-no-sample!))
      (finally (.countDown release) (reactive/close! sys)))))

(deftest frame-sampling-intervals-require-one-positive-whole-frame-count
  (let [sys (reactive/create-system {})]
    (try
      (doseq [interval [{:frames 0} {:frames -1} {:frames 1/2} {:frames "2"} {:frames 2 :beats 1}]]
        (is (thrown? clojure.lang.ExceptionInfo
                     (reactive/reg-cofx! sys ::remote {:mode :background :interval interval
                                                       :sample (constantly nil)}))))
      (finally (reactive/close! sys)))))

(deftest cycle-paced-coeffects-follow-the-selected-unwrapped-musical-position
  (let [model {:show-id :show :epoch 0 :frame-number 0 :value :steady
               :transport {:beat 0 :bpm 120 :playing? true}}
        sys (reactive/create-system model {:on-fault! (fn [_ _])})
        calls (LinkedBlockingQueue.) delivered (LinkedBlockingQueue.)
        release (CountDownLatch. 1) interrupted (CountDownLatch. 1)
        publish! (fn [db expected]
                   (is (= expected (some (fn [_]
                                           (reactive/publish! sys db)
                                           (.poll calls 20 TimeUnit/MILLISECONDS))
                                         (range 150)))))
        expect-value! (fn [expected]
                        (is (= expected (some (fn [_]
                                                (reactive/publish! sys)
                                                (.poll delivered 20 TimeUnit/MILLISECONDS))
                                              (range 150)))))
        no-sample! #(is (nil? (.poll calls 20 TimeUnit/MILLISECONDS)))]
    (try
      (reactive/reg-cofx! sys ::reading {:mode :background :interval {:cycles 1/2} :initial :waiting
                                        :cycle-position (fn [db] (get-in db [:oscillator :position]))
                                        :sample (fn [{:keys [oscillator value block?]}]
                                                  (.offer calls (:position oscillator))
                                                  (when block?
                                                    (try (.await release)
                                                         (catch InterruptedException e
                                                           (.countDown interrupted)
                                                           (throw e))))
                                                  value)})
      (reactive/reg-sub! sys ::reading (fn [{:keys [cofx]} _] (cofx ::reading)))
      (let [first-cycle (assoc-in model [:oscillator :position] 1/8)]
        (reactive/publish! sys first-cycle)
        (no-sample!)
        (reactive/publish! sys model)
        (let [a (reactive/acquire! sys [::reading] identity)
              b (reactive/acquire! sys [::reading] #(.offer delivered %))]
          (is (= [:waiting :waiting] [(:value a) (:value b)]))
          (no-sample!)
          (publish! first-cycle 1/8)
          (expect-value! :steady)
          (reactive/publish! sys (assoc first-cycle :frame-number 100 :time-ms 10000
                                                   :transport {:beat 25 :bpm 90 :playing? true}))
          (no-sample!)
          (reactive/publish! sys (assoc-in first-cycle [:oscillator :position] 49/100))
          (no-sample!)
          (publish! (assoc-in first-cycle [:oscillator :position] 1/2) 1/2)
          (reactive/publish! sys (-> first-cycle (assoc-in [:oscillator :position] 3/2)
                                    (assoc-in [:transport :playing?] false)))
          (no-sample!)
          (is (.isEmpty delivered) "An equal sampled value must not notify a reader.")
          ((:close! a))
          (publish! (-> first-cycle (assoc-in [:oscillator :position] 4) (assoc :value :jumped)) 4)
          (expect-value! :jumped)
          (no-sample!)
          (publish! (-> first-cycle (assoc-in [:oscillator :position] 9/2) (assoc :block? true)) 9/2)
          (reactive/publish! sys (assoc-in first-cycle [:oscillator :position] 5))
          (no-sample!)
          ((:close! b))
          (is (.await interrupted 3 TimeUnit/SECONDS))
          (reactive/publish! sys (assoc-in first-cycle [:oscillator :position] 11/2))
          (no-sample!)))
      (finally (.countDown release) (reactive/close! sys)))))

(deftest cycle-cadence-validation-and-projection-errors-use-the-coeffect-boundary
  (let [sys (reactive/create-system {:value 1} {:on-fault! (fn [_ _])})
        project (fn [db] (if (:fail? db) (throw (ex-info "Cycle source failed" {})) (:position db)))
        changes (LinkedBlockingQueue.)
        definition {:mode :background :interval {:cycles 1} :cycle-position project
                    :initial :waiting :sample (constantly :ready)}]
    (try
      (doseq [invalid [(dissoc definition :cycle-position)
                       (assoc definition :cycle-position :keyword)
                       (assoc definition :interval {:cycles 1 :beats 1})
                       (assoc definition :interval {:beats 1})
                       (assoc definition :mode :frame :interval nil)]
              :let [interval (:interval invalid)]]
        (is (thrown? clojure.lang.ExceptionInfo (reactive/reg-cofx! sys ::reading invalid)) (pr-str interval)))
      (doseq [value [0 -1 ##NaN ##Inf "2"]]
        (is (thrown? clojure.lang.ExceptionInfo
                     (reactive/reg-cofx! sys ::reading (assoc definition :interval {:cycles value})))))
      (reactive/reg-cofx! sys ::reading definition)
      (reactive/reg-sub! sys ::reading (fn [{:keys [cofx]} _] (cofx ::reading)))
      (reactive/reg-sub! sys ::healthy value-sub)
      (let [reading (reactive/acquire! sys [::reading] #(.offer changes %))
            healthy (reactive/acquire! sys [::healthy] identity)]
        (is (= :waiting (:value reading)))
        (doseq [db [{:fail? true :value 2} {:position ##NaN :value 3}]]
          (let [{:keys [faults]} (reactive/publish! sys db)]
            (is (= [{:stage :cofx :id ::reading}] (mapv #(select-keys % [:stage :id]) faults)))
            (is (= :waiting @(:signal reading)))
            (is (= (:value db) @(:signal healthy)))))
        (is (= :ready (some (fn [_]
                              (reactive/publish! sys {:position 1/4 :value 4})
                              (.poll changes 20 TimeUnit/MILLISECONDS))
                            (range 150))))
        ((:close! reading))
        ((:close! healthy)))
      (finally (reactive/close! sys)))))

(defn- assert-cycle-samples [interval positions]
  (let [sys (reactive/create-system {})
        calls (LinkedBlockingQueue.)]
    (try
      (reactive/reg-cofx! sys ::reading
                          {:mode :background :interval {:cycles interval} :cycle-position (fn [db] (:position db))
                           :sample (fn [db] (.offer calls (:position db)))})
      (reactive/reg-sub! sys ::reading (fn [{:keys [cofx]} _] (cofx ::reading)))
      (let [{:keys [close!]} (reactive/acquire! sys [::reading] identity)]
        (doseq [[position expected] positions]
          (testing (str "cycle position " position)
            (is (= (when expected position)
                   (some (fn [_]
                           (reactive/publish! sys {:position position})
                           (.poll calls 20 TimeUnit/MILLISECONDS))
                         (range (if expected 150 3)))))))
        (close!))
      (finally (reactive/close! sys)))))

(deftest exact-cycle-boundaries-use-floor-across-numeric-representations
  (assert-cycle-samples 1/5 [[-7/10 true] [-601/1000 false] [-3/5 true] [-599/1000 false]
                             [-1E-400M true] [0 true] [599/1000 true] [3/5 true]
                             [0.60M false] [0.61 false] [0.6 true] [3/5 true]
                             [(Math/nextDown 0.8) false] [0.8 true] [4/5 false]]))

(deftest exact-cycle-buckets-handle-underflowed-decimal-positions
  (let [half-min (.divide (BigDecimal. Double/MIN_VALUE) 2M)
        interval (rationalize (- half-min 1E-350M))
        position (- half-min 1E-351M)
        tiny (BigDecimal. BigInteger/ONE Integer/MAX_VALUE)]
    (is (= Double/MIN_VALUE (double interval)))
    (is (zero? (double position)))
    (assert-cycle-samples interval [[tiny true] [0 false] [position true] [interval false]
                                    [(- tiny) true] [(- interval) false] [(- position) true]])))

(deftest cycle-projection-linkage-errors-are-isolated-at-acquisition-and-publication
  (let [reported (atom [])
        sys (reactive/create-system {:failure "initial linkage" :value 1}
                                    {:on-fault! (fn [fault error] (swap! reported conj [fault (ex-cause error)]))})
        project (fn [{:keys [failure position]}]
                  (when failure (throw (NoClassDefFoundError. failure)))
                  position)]
    (try
      (reactive/reg-cofx! sys ::reading {:mode :background :interval {:cycles 1} :cycle-position project :initial :waiting
                                        :sample (constantly :ready)})
      (reactive/reg-sub! sys ::reading (fn [{:keys [cofx]} _] (cofx ::reading)) {:fallback :waiting})
      (reactive/reg-sub! sys ::healthy value-sub)
      (let [healthy (reactive/acquire! sys [::healthy] identity)
            reading (reactive/acquire! sys [::reading] identity)]
        (is (true? (:available? reading)))
        (is (= :waiting (:value reading)))
        (is (= 1 (:value healthy)))
        (is (= [{:stage :cofx :id ::reading :message "initial linkage"}]
               (mapv #(select-keys % [:stage :id :message]) (reactive/faults sys))))
        (reactive/publish! sys {:value 2})
        (let [{:keys [faults]} (reactive/publish! sys {:failure "linked during publish" :value 3})]
          (is (= [{:stage :cofx :id ::reading :message "linked during publish"}]
                 (mapv #(select-keys % [:stage :id :message]) faults)))
          (is (= [[NoClassDefFoundError "initial linkage"] [NoClassDefFoundError "linked during publish"]]
                 (mapv (fn [[_ cause]] [(class cause) (ex-message cause)]) @reported)))
          (is (= :waiting @(:signal reading)))
          (is (= 3 @(:signal healthy))))
        ((:close! reading))
        ((:close! healthy)))
      (finally (reactive/close! sys)))))

(deftest cycle-projection-interruption-and-vm-failure-reach-the-owner
  (let [sys (reactive/create-system {:phase :initial})
        interrupt (InterruptedException. "owner interrupted")
        fatal (ex-info "wrapped VM failure" {} (InternalError. "VM failed"))
        project (fn [{:keys [phase]}]
                  (case phase :initial (throw interrupt) :fatal (throw fatal) nil))]
    (try
      (reactive/reg-cofx! sys ::reading {:mode :background :interval {:cycles 1} :cycle-position project
                                        :sample (constantly :ready)})
      (reactive/reg-sub! sys ::reading (fn [{:keys [cofx]} _] (cofx ::reading)))
      (is (identical? interrupt (try (reactive/acquire! sys [::reading] identity) (catch Throwable e e))))
      (is (false? (reactive/demanded? sys #{::reading})))
      (reactive/publish! sys {:phase :normal})
      (let [{:keys [close!]} (reactive/acquire! sys [::reading] identity)]
        (is (identical? fatal (try (reactive/publish! sys {:phase :fatal}) (catch Throwable e e))))
        (is (empty? (reactive/faults sys)))
        (close!))
      (finally (reactive/close! sys)))))

(defn- assert-old-epoch-sample-is-retired [cadence]
  (let [model {:show-id :show :epoch 0 :frame-number 0}
        sys (reactive/create-system model)
        old-started (CountDownLatch. 1) old-interrupted (CountDownLatch. 1)
        release-old (CountDownLatch. 1) new-started (CountDownLatch. 1)
        release-new (CountDownLatch. 1) probe-started (CountDownLatch. 1)
        changes (LinkedBlockingQueue.)]
    (try
      (reactive/reg-cofx! sys ::reading
                          (assoc cadence :mode :background :initial :waiting
                                 :sample (fn [{:keys [epoch]}]
                                           (if (zero? epoch)
                                             (do
                                               (.countDown old-started)
                                               (try (.await release-old)
                                                    (catch InterruptedException _
                                                      (.countDown old-interrupted)
                                                      (.await release-old)))
                                               :stale)
                                             (do
                                               (.countDown new-started)
                                               (.await release-new)
                                               :current)))))
      (reactive/reg-sub! sys ::reading (fn [{:keys [cofx]} _] (cofx ::reading)))
      (reactive/reg-fx! sys ::launch
                        (fn [_ value _]
                          (when (#{:stale :current} value)
                            {:op :cue/launch :cue-id value})))
      (reactive/watch! sys ::watch-reading [::reading] ::launch)
      (let [{:keys [signal]} (reactive/acquire! sys [::reading] #(.offer changes %))]
        (is (.await old-started 3 TimeUnit/SECONDS))
        (reactive/publish! sys)
        (reactive/publish! sys (update model :epoch inc))
        (is (.await old-interrupted 3 TimeUnit/SECONDS))
        (is (.await new-started 3 TimeUnit/SECONDS))
        ;; Both sampler threads are occupied. The probe can only start once
        ;; the old worker has handled its result because the new one stays held.
        (reactive/reg-cofx! sys ::probe (assoc cadence :mode :background
                                             :sample (fn [_] (.countDown probe-started))))
        (reactive/reg-sub! sys ::probe (fn [{:keys [cofx]} _] (cofx ::probe)))
        (let [{:keys [close!]} (reactive/acquire! sys [::probe] identity)]
          (.countDown release-old)
          (is (.await probe-started 3 TimeUnit/SECONDS))
          (reactive/publish! sys)
          (is (= :waiting @signal))
          (is (.isEmpty changes))
          (is (empty? (reactive/drain-actions! sys)))
          (close!))
        (.countDown release-new)
        (is (= :current (some (fn [_]
                                (reactive/publish! sys)
                                (.poll changes 20 TimeUnit/MILLISECONDS))
                              (range 150))))
        (reactive/publish! sys)
        (is (.isEmpty changes))
        (is (= [{:op :cue/launch :cue-id :current}] (reactive/drain-actions! sys))))
      (finally
        (.countDown release-old)
        (.countDown release-new)
        (reactive/close! sys)))))

(deftest frame-paced-samples-from-an-old-epoch-cannot-reach-retained-watchers
  (assert-old-epoch-sample-is-retired {:interval {:frames 2}}))

(deftest cycle-paced-samples-from-an-old-epoch-cannot-reach-retained-watchers
  (assert-old-epoch-sample-is-retired {:interval {:cycles 1/2} :cycle-position (constantly 0)}))

(defn- transport-db [beat & {:as extra}]
  (merge {:show-id :show :epoch 0 :frame-number 0 :value :steady
          :transport {:beat beat :bpm 120 :playing? true}}
         extra))

(defn- oscillator-sampler
  "Publish db. When a sample is expected, republish until the sampler reports
  it and return the sampled beat. Otherwise publish once and return nil
  without waiting. Each silent step is proven by the next expected one: a
  source has at most one outstanding read and a busy source retries, so an
  unexpected read would be reported first and fail that assertion."
  [sys ^LinkedBlockingQueue calls]
  (fn [db expected?]
    (if expected?
      (some (fn [_]
              (reactive/publish! sys db)
              (.poll calls 20 TimeUnit/MILLISECONDS))
            (range 250))
      (do (reactive/publish! sys db) nil))))

(deftest named-oscillator-cycles-share-one-sampler-and-skip-missed-boundaries
  (let [sys (reactive/create-system (transport-db 0) {:on-fault! (fn [_ _])})
        calls (LinkedBlockingQueue.) levels (LinkedBlockingQueue.)
        release (CountDownLatch. 1) interrupted (CountDownLatch. 1)
        sampled (oscillator-sampler sys calls)]
    (try
      ;; position = 1/4 + beat/2, so quarter-cycle buckets change every half beat.
      (is (= :groove (reactive/reg-oscillator! sys :groove {:period {:beats 2} :phase 1/4})))
      (reactive/reg-cofx! sys ::reading {:mode :background :interval {:cycles 1/4} :oscillator :groove
                                        :initial :waiting
                                        :sample (fn [{:keys [transport value block?]}]
                                                  (.offer calls (:beat transport))
                                                  (when block?
                                                    (try (.await release)
                                                         (catch InterruptedException e
                                                           (.countDown interrupted)
                                                           (throw e))))
                                                  [(:beat transport) value])})
      (reactive/reg-sub! sys ::reading (fn [{:keys [cofx]} _] (cofx ::reading)))
      (reactive/reg-sub! sys ::level (fn [{:keys [cofx]} _] (let [v (cofx ::reading)] (if (vector? v) (second v) v))))
      (is (nil? (sampled (transport-db -1) false)) "Nothing samples before a reader exists.")
      (is (nil? (sampled (transport-db 0) false)))
      (let [a (reactive/acquire! sys [::reading] identity)
            b (reactive/acquire! sys [::level] #(.offer levels %))]
        (is (= 1/4 (reactive/oscillator-position sys :groove)))
        (testing "both readers share the first bucket's one sample"
          (is (= 0 (sampled (transport-db 0) true)))
          (is (nil? (sampled (transport-db 1/4) false)))
          ;; The first sample can land before the second lease reads it.
          (is (= :steady (some (fn [_] (reactive/publish! sys) (#{:steady} @(:signal b))) (range 150))))
          (.clear levels))
        (testing "each crossed boundary requests one sample"
          (is (= 1/2 (sampled (transport-db 1/2) true)))
          (is (nil? (sampled (transport-db 3/4) false))))
        (testing "a tempo change keeps boundaries in cycles"
          (is (nil? (sampled (assoc-in (transport-db 7/8) [:transport :bpm] 90) false)))
          (is (= 1 (sampled (assoc-in (transport-db 1) [:transport :bpm] 90) true))))
        (testing "several boundaries in one frame request one sample, like skipped frames"
          (is (= 4 (sampled (transport-db 4) true)))
          (is (nil? (sampled (transport-db 17/4) false))))
        (testing "a seek inside the bucket is silent; a seek elsewhere samples once"
          (is (nil? (sampled (transport-db 33/8) false)))
          (is (= 2 (sampled (transport-db 2 :frame-number 1) true)))
          (is (nil? (sampled (transport-db 2 :frame-number 2) false)))
          (is (nil? (sampled (transport-db 9/4 :frame-number 3) false))))
        (testing "a stopped transport holds the bucket"
          (is (nil? (sampled (assoc-in (transport-db 3) [:transport :playing?] false) false))))
        ((:close! a))
        (testing "the remaining reader keeps demand alive"
          (is (= 5 (sampled (transport-db 5 :value :moved) true)))
          (is (= :moved (some (fn [_] (reactive/publish! sys) (.poll levels 20 TimeUnit/MILLISECONDS)) (range 150)))))
        (is (= 11/2 (sampled (transport-db 11/2 :block? true) true)))
        ((:close! b))
        (is (.await interrupted 3 TimeUnit/SECONDS) "The last lease cancels the running sample.")
        (is (false? (reactive/demanded? sys #{::reading})))
        (is (nil? (sampled (transport-db 8) false)))
        (is (nil? (sampled (transport-db 9) false)))
        (reactive/publish! sys (transport-db 10))
        (let [{:keys [close!]} (reactive/acquire! sys [::reading] identity)]
          (is (= 10 (.poll calls 3 TimeUnit/SECONDS))
              "A fresh lease's first read is the next one, so released frames started none.")
          (close!)))
      (finally (.countDown release) (reactive/close! sys)))))

(deftest named-oscillator-validation-and-renames-are-explicit
  (let [sys (reactive/create-system (transport-db 0) {:on-fault! (fn [_ _])})
        calls (LinkedBlockingQueue.)
        sampled (oscillator-sampler sys calls)
        definition {:mode :background :interval {:cycles 1} :oscillator :groove :initial :waiting
                    :sample (fn [{:keys [transport]}] (.offer calls (:beat transport)) (:beat transport))}]
    (try
      (doseq [invalid [nil {} {:period {:ms 500}} {:period {:beats 0}} {:period {:beats 1 :bars 1}}
                       {:period {:beats ##Inf}} {:period {:beats 1} :phase ##NaN} {:period {:beats 1} :rate 2}]]
        (is (= ::reactive/invalid-oscillator (error-type #(reactive/reg-oscillator! sys :groove invalid)))
            (pr-str invalid)))
      (is (= ::reactive/invalid-oscillator (error-type #(reactive/reg-oscillator! sys "groove" {:period {:beats 1}}))))
      (let [error (try (reactive/reg-cofx! sys ::reading definition) nil (catch clojure.lang.ExceptionInfo e e))]
        (is (= ::reactive/unknown-oscillator (:type (ex-data error))))
        (is (= :groove (:oscillator (ex-data error))))
        (is (re-find #"Unknown reactive oscillator :groove" (ex-message error))))
      (reactive/reg-oscillator! sys :groove {:period {:bars 1}})
      (doseq [invalid [(assoc definition :oscillator "groove")
                       (assoc definition :interval {:beats 1})
                       (assoc definition :mode :frame :interval nil)
                       (assoc definition :cycle-position :position)]]
        (is (thrown? clojure.lang.ExceptionInfo (reactive/reg-cofx! sys ::reading invalid)) (pr-str invalid)))
      (reactive/reg-cofx! sys ::reading definition)
      (reactive/reg-sub! sys ::reading (fn [{:keys [cofx]} _] (cofx ::reading)))
      (let [{:keys [signal close!]} (reactive/acquire! sys [::reading] identity)]
        (is (= 0 (sampled (transport-db 0) true)))
        (is (= 0 (some (fn [_] (reactive/publish! sys) (when (= 0 @signal) 0)) (range 150))))
        (testing "renaming the oscillator reports a clear fault and keeps the last value"
          (is (true? (reactive/remove-oscillator! sys :groove)))
          (reactive/reg-oscillator! sys :swing {:period {:bars 1}})
          (is (= {:swing {:period {:bars 1} :phase 0}} (reactive/oscillators sys)))
          (let [{:keys [faults]} (reactive/publish! sys (transport-db 8))]
            (is (= [{:stage :cofx :id ::reading}] (mapv #(select-keys % [:stage :id]) faults)))
            (is (re-find #"Unknown reactive oscillator :groove; registered oscillators: \[:swing\]"
                         (:message (first faults)))))
          (is (empty? (:faults (reactive/publish! sys (transport-db 9)))) "The fault is reported once.")
          (is (= 0 @signal)))
        (testing "registering the name again resumes from the committed phase"
          (reactive/reg-oscillator! sys :groove {:period {:bars 1}})
          (is (= 12 (sampled (transport-db 12) true))))
        (close!))
      (finally (reactive/close! sys)))))

(defn- replay-oscillator-samples [frames]
  (let [sys (reactive/create-system (transport-db 0))
        calls (LinkedBlockingQueue.)
        sampled (oscillator-sampler sys calls)]
    (try
      ;; One 7/8 bar is 7/2 quarter-note beats, so the period is normalized by
      ;; the committed meter rather than assuming four beats.
      (reactive/reg-oscillator! sys :groove {:period {:bars 1} :phase 1/8})
      (reactive/reg-cofx! sys ::reading {:mode :background :interval {:cycles 1/4} :oscillator :groove
                                        :sample (fn [{:keys [transport]}] (.offer calls (:beat transport)))})
      (reactive/reg-sub! sys ::reading (fn [{:keys [cofx]} _] (cofx ::reading)))
      (let [{:keys [close!]} (reactive/acquire! sys [::reading] identity)]
        (try
          (mapv (fn [[beat expected?]]
                  (sampled (assoc-in (transport-db beat) [:transport :meter] {:beats-per-bar 7/2}) expected?))
                frames)
          (finally (close!))))
      (finally (reactive/close! sys)))))

(deftest named-oscillator-sampling-replays-deterministically
  ;; position = 1/8 + 2 beat / 7; quarter-cycle boundaries fall at beats 7/16 + 7k/8.
  (let [frames [[0 true] [3/8 false] [7/16 true] [1 false] [21/16 true] [5 true] [41/8 false] [4 true]]
        first-run (replay-oscillator-samples frames)]
    (is (= [0 nil 7/16 nil 21/16 5 nil 4] first-run))
    (is (= first-run (replay-oscillator-samples frames)))))

(deftest named-oscillator-bar-periods-continue-across-meter-changes
  (let [sys (reactive/create-system (transport-db 0))
        calls (LinkedBlockingQueue.)
        sampled (oscillator-sampler sys calls)
        at (fn [beat beats-per-bar] (assoc-in (transport-db beat) [:transport :meter] {:beats-per-bar beats-per-bar}))]
    (try
      (reactive/reg-oscillator! sys :bar {:period {:bars 1}})
      (reactive/reg-cofx! sys ::reading {:mode :background :interval {:cycles 1} :oscillator :bar
                                        :sample (fn [{:keys [transport]}] (.offer calls (:beat transport)))})
      (reactive/reg-sub! sys ::reading (fn [{:keys [cofx]} _] (cofx ::reading)))
      (let [{:keys [close!]} (reactive/acquire! sys [::reading] identity)]
        (is (= 0 (sampled (at 0 4) true)))
        (is (= 639/10 (sampled (at 639/10 4) true)))
        (testing "4/4 to 7/8 at beat 64 continues from bar 16 instead of jumping to 18.29"
          (is (= 64.0M (sampled (at 64.0M 7/2) true)))
          (is (= 16 (reactive/oscillator-position sys :bar)))
          (is (nil? (sampled (at 66.5M 7/2) false)))
          (is (= 117/7 (reactive/oscillator-position sys :bar)) "A decimal beat stays exact.")
          (is (= 135/2 (sampled (at 135/2 7/2) true))))
        (testing "7/8 back to 4/4 never moves backwards"
          (is (nil? (sampled (at 70 4) false)))
          (is (= 124/7 (reactive/oscillator-position sys :bar)))
          (is (= 72 (sampled (at 72 4) true)))
          (is (= 255/14 (reactive/oscillator-position sys :bar))))
        (testing "a new epoch restarts at phase + beat / period"
          (is (= 8 (sampled (assoc (at 8 4) :epoch 1) true)))
          (is (= 2 (reactive/oscillator-position sys :bar))))
        (is (empty? (reactive/faults sys)))
        (close!))
      (finally (reactive/close! sys)))))

(deftest replacing-an-oscillator-definition-samples-again-in-the-same-bucket
  (let [sys (reactive/create-system (transport-db 0) {:on-fault! (fn [_ _])})
        calls (LinkedBlockingQueue.)
        sampled (oscillator-sampler sys calls)]
    (try
      (reactive/reg-oscillator! sys :pulse {:period {:beats 4}})
      (reactive/reg-cofx! sys ::reading {:mode :background :interval {:cycles 1} :oscillator :pulse
                                        :sample (fn [{:keys [transport]}] (.offer calls (:beat transport)))})
      (reactive/reg-sub! sys ::reading (fn [{:keys [cofx]} _] (cofx ::reading)))
      (let [{:keys [close!]} (reactive/acquire! sys [::reading] identity)]
        (is (= 0 (sampled (transport-db 0) true)))
        (reactive/reg-oscillator! sys :pulse {:period {:beats 4}})
        (is (nil? (sampled (transport-db 1) false)) "An identical definition keeps its bucket.")
        (testing "a changed period samples although bucket 0 is unchanged"
          (reactive/reg-oscillator! sys :pulse {:period {:beats 2}})
          (is (= 3/2 (sampled (transport-db 3/2) true)))
          (is (= 3/4 (reactive/oscillator-position sys :pulse))))
        (testing "remove and register again also samples"
          (reactive/remove-oscillator! sys :pulse)
          (is (= 1 (count (:faults (reactive/publish! sys (transport-db 7/4))))))
          (reactive/reg-oscillator! sys :pulse {:period {:beats 2}})
          (is (= 7/4 (sampled (transport-db 7/4) true))))
        (close!))
      (finally (reactive/close! sys)))))

(deftest invalid-db-does-not-stop-independent-sources-or-drop-diagnostics
  (let [system (reactive/create-system {:value 1} {:on-fault! (fn [_ _])}) src (reactive/ratom system ::x 1)]
    (set-validator! (reactive/db-signal system) #(pos-int? (:value %)))
    (reactive/reg-sub! system ::source (fn [_ _] @src))
    (let [lease (reactive/acquire! system [::source] identity)]
      (reset! src 2)
      (let [batch (reactive/publish! system {:value -1})]
        (is (= [:source] (mapv :stage (:faults batch))))
        (is (= 2 @(:signal lease)))
        (is (= {:value 1} @(reactive/db-signal system))))
      (is (empty? (:faults (reactive/publish! system))))
      ((:close! lease)))))

(deftest untrusted-var-restoration-requires-local-registration-or-explicit-allowlist
  (let [empty (reactive/create-system {:value 2}) known (reactive/create-system {})
        data {:registrations [value-definition]}]
    (reactive/reg-sub! known ::value value-sub value-definition)
    (is (= ::registry/untrusted-var (error-type #(reactive/restore! empty data))))
    (is (= ::registry/untrusted-var
           (error-type #(reactive/restore! empty (assoc-in data [:registrations 0 :id] ::other)
                                          {:local-system known}))))
    (reactive/restore! empty data {:local-system known})
    (is (= 2 @(reactive/subscribe empty [::value])))
    (reactive/restore! empty data)
    (is (= 2 @(reactive/subscribe empty [::value])))
    (let [fresh (reactive/create-system {:value 4})]
      (reactive/restore! fresh data {:allowed-vars #{'afterglow.reactive-test/value-sub}})
      (is (= 4 @(reactive/subscribe fresh [::value]))))))

(deftest replacing-a-live-query-with-a-cyclic-dependency-retains-healthy-siblings
  (let [system (reactive/create-system {:n 1})]
    (try
      (reactive/reg-sub! system ::a (fn [_ _] 3))
      (reactive/reg-sub! system ::b (fn [{:keys [subscribe]} _] (inc @(subscribe [::a]))))
      (reactive/reg-sub! system ::independent (fn [{:keys [db]} _] (:n @db)))
      (let [a (reactive/subscribe system [::a])
            b (reactive/subscribe system [::b])
            independent (reactive/subscribe system [::independent])]
        (is (= [3 4 1] [@a @b @independent]))
        (reactive/reg-sub! system ::a (fn [{:keys [subscribe]} _] (inc @(subscribe [::b]))))
        (let [publication (reactive/publish! system {:n 2})]
          (is (= [3 4 2] [@a @b @independent]))
          (is (= ::a (:id (first (:faults publication))))))
        (reactive/reg-sub! system ::a (fn [_ _] 8))
        (reactive/publish! system {:n 3})
        (is (= [8 9 3] [@a @b @independent])))
      (finally (reactive/close! system)))))

(deftest previously-saved-detached-repl-can-restore-core-and-captured-values
  (let [definition {:id ::level :kind :sub
                    :implementation {:type :source :namespace "example.session_12345678_abcd_1234_abcd_123456789abc"
                                     :form "(fn [_ _] (* factor 2))" :bindings {"factor" 3}}}]
    (is (thrown? clojure.lang.ExceptionInfo (registry/resolve-handler definition {})))
    (let [handler (registry/resolve-handler definition {:trusted-source? true})]
      (is (= 6 (handler {} [::level]))))))

(deftest releasing-and-reacquiring-a-peer-during-delivery
  (let [system (reactive/create-system {:value 1})
        leases (atom {}) calls (atom [])]
    (try
      (reactive/reg-sub! system ::lease (fn [{:keys [db]} _] (:value @db)))
      (doseq [id [0 1]]
        (let [peer (- 1 id)
              on-change (fn [value]
                          (swap! calls conj [id value])
                          ((:close! (get @leases peer)))
                          (swap! leases assoc peer
                                 (reactive/acquire! system [::lease peer]
                                                    #(swap! calls conj [:replacement %]))))]
          (swap! leases assoc id (reactive/acquire! system [::lease id] on-change))))
      (is (integer? (:generation (reactive/publish! system {:value 2}))))
      (is (= 1 (count @calls)))
      (is (= 2 (second (first @calls))))
      (is (every? #(= 2 @(:signal %)) (vals @leases)))
      (finally (reactive/close! system)))))

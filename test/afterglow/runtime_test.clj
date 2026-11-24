(ns afterglow.runtime-test
  (:require [afterglow.runtime :as runtime]
            [clojure.test :refer [deftest is testing]])
  (:import [java.util.concurrent Callable CountDownLatch ExecutorCompletionService
            Executors TimeUnit]))

(defn- instance
  ([id step] (instance id 0 0 {} step))
  ([id priority order state step]
   {:id id :priority priority :order order :state state :step step}))

(defn- frame
  [& instances]
  {:frame {:number 42 :elapsed-ms 500 :inputs {:level 0.75}}
   :effects (vec instances)})

(defn- contribution
  [context]
  (-> context
      (update :assignments conj [(:effect-id context) (:state context)])
      (update :intents conj {:source (:effect-id context) :event :observed})))

(deftest middleware-state-and-input-snapshot
  (let [advance #(update-in % [:state :count] + (get-in % [:frame :number]))
        effect (instance :pulse 0 0 {:count 1} (comp contribution advance))
        context (assoc (frame effect) :rig-version 9 :assignments [:old] :intents [:old])
        result (runtime/render-frame context)
        next-result (runtime/render-frame (assoc-in result [:frame :number] 1))]
    (is (= [[:pulse {:count 43}]] (:assignments result)))
    (is (= [{:source :pulse :event :observed}] (:intents result)))
    (is (= {:count 43} (get-in result [:effects 0 :state])))
    (is (= {:count 44} (get-in next-result [:effects 0 :state])))
    (is (= 9 (:rig-version result)))
    (is (= (:frame context) (:frame result)))
    (is (= effect (first (:effects context))) "Input instance was not mutated")
    (is (= [:old] (:assignments context)))
    (is (= result (runtime/render-frame context)) "Identical input replays identically")))

(deftest each-effect-owns-its-state
  (let [step #(-> % (update-in [:state :count] inc) contribution)
        context (frame (instance :a 0 0 {:count 1} step)
                       (instance :b 0 1 {:count 100} step))
        result (runtime/render-frame context)]
    (is (= [[:a {:count 2}] [:b {:count 101}]] (:assignments result)))
    (is (= [{:count 1} {:count 100}] (mapv :state (:effects context))))
    (is (= [{:count 2} {:count 101}] (mapv :state (:effects result))))))

(deftest priorities-launch-order-and-ties
  (let [instances [(instance :high 3 0 {} contribution)
                   (instance :later 0 2 {} contribution)
                   (instance :earlier 0 1 {} contribution)
                   (instance :tie 0 1 {} contribution)
                   (instance :low -1 9 {} contribution)]
        context (apply frame instances)
        result (runtime/render-frame context)
        expected [:low :earlier :tie :later :high]]
    (is (= expected (mapv first (:assignments result))))
    (is (= expected (mapv :source (:intents result))))
    (is (= (mapv :id instances) (mapv :id (:effects result)))
        "Evaluation precedence does not reorder stored instances")
    (is (= result (runtime/render-frame context #(reverse (mapv %1 %2))))
        "Worker return order cannot change precedence")))

(deftest final-frame-contributions-and-removal
  (let [finish #(-> % contribution (assoc :done? true))
        context (frame (instance :ending finish) (instance :running identity))
        result (runtime/render-frame context)
        next-result (runtime/render-frame result)]
    (is (= [[:ending {}]] (:assignments result)))
    (is (= [{:source :ending :event :observed}] (:intents result)))
    (is (= [{:intent {:source :ending :event :observed} :source {:instance-id :ending}}]
           (:intent-emissions result)))
    (is (= [:running] (mapv :id (:effects result))))
    (is (= [] (:assignments next-result)))
    (is (= [] (:intents next-result)))
    (is (not (contains? next-result :intent-emissions)))))

(deftest effect-cannot-replace-shared-frame-or-instance-identity
  (let [context (frame (instance :original #(assoc % :frame {:number -1}
                                                   :effect-id :impostor)))
        result (runtime/render-frame context)]
    (is (= (:frame context) (:frame result)))
    (is (= :original (get-in result [:effects 0 :id])))))

(deftest parallel-completion-order-matches-serial
  (let [pool (Executors/newFixedThreadPool 2)
        gate (CountDownLatch. 1)
        completion (ExecutorCompletionService. pool)
        context (frame (instance :slow 0 0 {:count 1} contribution)
                       (instance :fast 0 1 {:count 2} contribution))
        map-work (fn [f instances]
                   (doseq [item instances]
                     (.submit completion
                              ^Callable
                              (reify Callable
                                (call [_]
                                  (when (= :slow (:id item))
                                    (when-not (.await gate 5 TimeUnit/SECONDS)
                                      (throw (ex-info "Test gate timed out" {}))))
                                  (f item)))))
                   (let [first-task (.poll completion 5 TimeUnit/SECONDS)]
                     (when-not first-task
                       (throw (ex-info "Test worker timed out" {})))
                     (let [first-result (.get first-task)]
                       (is (= :fast (:id first-result))
                           "The later effect actually completed first on a worker")
                       (.countDown gate)
                       (let [last-task (.poll completion 5 TimeUnit/SECONDS)]
                         (when-not last-task
                           (throw (ex-info "Test worker timed out" {})))
                         [first-result (.get last-task)]))))]
    (try
      (is (= (runtime/render-frame context)
             (runtime/render-frame context map-work)))
      (finally
        (.countDown gate)
        (.shutdownNow pool)
        (.awaitTermination pool 5 TimeUnit/SECONDS)))))

(deftest duplicate-identities-and-invalid-instance-data
  (testing "Reject ambiguity before running any step"
    (let [must-not-run #(throw (ex-info "Unexpected evaluation" {}))]
      (is (= ::runtime/duplicate-effect-id
             (try
               (runtime/render-frame (frame (instance :same must-not-run)
                                            (instance :same must-not-run)))
               (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))))
  (doseq [effect [(assoc (instance :a identity) :priority Double/NaN)
                  (assoc (instance :a identity) :priority Double/POSITIVE_INFINITY)
                  (assoc (instance :a identity) :order -1)
                  (dissoc (instance :a identity) :state)
                  (assoc (instance :a identity) :id nil)]]
    (is (thrown? clojure.lang.ExceptionInfo (runtime/render-frame (frame effect)))))
  (is (thrown? clojure.lang.ExceptionInfo
               (runtime/render-frame {:frame {} :effects #{}}))))

(deftest failures-cannot-return-a-partially-updated-context
  (let [context (frame (instance :ok #(update % :state assoc :updated true))
                       (instance :bad #(assoc % :assignments '(not-a-vector))))]
    (is (= {:type ::runtime/invalid-result :effect-id :bad}
           (try (runtime/render-frame context)
                (catch clojure.lang.ExceptionInfo e (ex-data e)))))
    (is (= [{} {}] (mapv :state (:effects context)))))
  (doseq [step [#(dissoc % :state)
               #(assoc % :done? :yes)
               #(assoc % :intents nil)]]
    (is (thrown? clojure.lang.ExceptionInfo
                 (runtime/render-frame (frame (instance :bad step))))))
  (let [cause (ex-info "Effect bug" {:detail :test})
        context (frame (instance :bad (fn [_] (throw cause))))]
    (try
      (runtime/render-frame context)
      (is false "Expected failure")
      (catch clojure.lang.ExceptionInfo e
        (is (= ::runtime/step-failed (:type (ex-data e))))
        (is (= :bad (:effect-id (ex-data e))))
        (is (identical? cause (.getCause e)))))))

(deftest incomplete-or-duplicate-executor-results-are-rejected
  (let [context (frame (instance :a identity) (instance :b identity))]
    (is (thrown? clojure.lang.ExceptionInfo
                 (runtime/render-frame context (fn [f jobs] [(f (first jobs))]))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (runtime/render-frame context
                                       (fn [f jobs]
                                         (let [result (f (first jobs))]
                                           [result result])))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (runtime/render-frame context
                                       (fn [f jobs]
                                         (mapv #(assoc (f %) :id :unknown) jobs)))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (runtime/render-frame context
                                       (fn [_ jobs]
                                         (mapv #(select-keys % [:id]) jobs)))))))

(deftest empty-frame-has-empty-outputs
  (is (= {:frame {} :effects [] :assignments [] :contributions [] :intents []}
         (runtime/render-frame {:frame {} :effects []}))))


(deftest mixed-blocks-retain-middleware-effect-and-worker-order
  (let [step (fn [ctx]
               (-> ctx
                   (update :assignments conj :before)
                   (runtime/append-contributions [{:kind :batch :batch {:tag (:effect-id ctx)}}])
                   (update :assignments conj :after)))
        context (frame (instance :later 2 1 {} step) (instance :earlier 0 2 {} step))
        result (runtime/render-frame context)]
    (is (nil? (:assignments result)) "No partial ordinary-only aggregate may escape")
    (is (= [{:kind :assignments :assignments [:before]}
            {:kind :batch :batch {:tag :earlier}}
            {:kind :assignments :assignments [:after]}
            {:kind :assignments :assignments [:before]}
            {:kind :batch :batch {:tag :later}}
            {:kind :assignments :assignments [:after]}] (:contributions result)))
    (is (= result (runtime/render-frame context #(reverse (mapv %1 %2))))))
  (doseq [blocks [nil {} [{:kind :unknown}] [{:kind :batch :batch []}]
                  [{:kind :assignments :assignments nil}]]]
    (is (thrown? clojure.lang.ExceptionInfo
                 (runtime/render-frame (frame (instance :bad #(assoc % :contributions blocks))))))))

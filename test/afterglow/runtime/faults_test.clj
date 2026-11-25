(ns afterglow.runtime.faults-test
  (:require [clojure.test :refer [deftest is testing]]
            [afterglow.runtime.engine :as engine]
            [afterglow.runtime.engine-test :as fixture]
            [afterglow.runtime.executor :as executor]
            [afterglow.runtime.replay :as replay]
            [afterglow.control.model :as control]))

(defn- invoke [show t compile] (engine/advance show {:time-ms t} compile))

(defn- calls-compiler [calls behavior]
  (fn [definition]
    (fn [context]
      (swap! calls conj [(get-in context [:instance :id]) (:version definition)])
      (behavior definition context))))

(deftest failed-attempts-are-quarantined-while-healthy-state-and-order-continue
  (let [calls (atom [])
        compile (calls-compiler calls
                 (fn [definition context]
                   (if (= "broken" (get-in context [:instance :id]))
                     (throw (AssertionError. "Edited expression is invalid"))
                     ((fixture/compiler definition) context))))
        show (fixture/model (fixture/instance "broken" :order 0) (fixture/instance "healthy" :order 1))
        first (invoke show 10 compile)
        second (invoke (:model first) 20 compile)]
    (is (= [["broken" 1] ["healthy" 1] ["healthy" 1]] @calls))
    (is (= {:frames 0} (get-in second [:model :instances "broken" :state])))
    (is (= {:frames 2} (get-in second [:model :instances "healthy" :state])))
    (is (= ["healthy"] (mapv :source (:assignments second))))
    (is (= [:effect/failed] (mapv :type (:fault-events first))))
    (is (empty? (:fault-events second)))
    (is (= 1 (count (get-in second [:model :variables :runtime :events]))))
    (is (= "java.lang.AssertionError" (get-in first [:model :instances "broken" :fault :causes 0 :class])))))

(deftest malformed-results-discard-state-intents-and-blocks
  (doseq [bad [(fn [c] (assoc c :done? :yes :state :wrong))
               (fn [c] (assoc c :assignments '(invalid) :intents [{:type :must-not-run}]))
               (fn [c] (assoc c :contributions [{:kind :wrong}] :state :wrong))]]
    (let [result (invoke (fixture/model (fixture/instance "broken")) 10 (fn [_] bad))]
      (is (= {:frames 0} (get-in result [:model :instances "broken" :state])))
      (is (empty? (:contributions result)))
      (is (= [:effect/failed] (mapv :type (:intents result)))))))

(deftest candidate-compile-and-evaluate-failures-retain-live-last-good-code
  (doseq [stage [:compile :evaluate]]
    (let [calls (atom [])
          compile (fn [definition]
                    (swap! calls conj [:compile (:version definition)])
                    (when (and (= stage :compile) (= 2 (:version definition)))
                      (throw (ex-info "Bad candidate compile" {})))
                    (fn [context]
                      (swap! calls conj [:step (:version definition)])
                      (when (= 2 (:version definition)) (throw (NoClassDefFoundError. "Edited dependency")))
                      ((fixture/compiler definition) context)))
          show (-> (fixture/model (fixture/instance "live" :reload-policy :preserve-state))
                   (assoc-in [:registry :effects :pulse :version] 2))
          failed (invoke show 10 compile)
          continued (invoke (:model failed) 20 compile)
          recovered (invoke (assoc-in (:model continued) [:registry :effects :pulse :version] 3) 30 compile)]
      (is (= [1] (mapv :definition-version (:assignments failed))))
      (is (= [1] (mapv :definition-version (:assignments continued))))
      (is (= 1 (count (filter #{[:compile 2]} @calls))))
      (is (= stage (get-in failed [:model :instances "live" :reload-fault :stage])))
      (is (= {:frames 3} (get-in recovered [:model :instances "live" :state])))
      (is (nil? (get-in recovered [:model :instances "live" :reload-fault])))
      (is (= [:effect/recovered] (mapv :type (:fault-events recovered)))))))

(deftest rejected-candidate-and-failed-last-good-are-independently-suppressed
  (let [calls (atom []) compile (calls-compiler calls (fn [_ _] (throw (ex-info "Both bad" {}))))
        show (-> (fixture/model (fixture/instance "live" :reload-policy :preserve-state))
                 (assoc-in [:registry :effects :pulse :version] 2))
        failed (invoke show 10 compile)
        suppressed (invoke (:model failed) 20 compile)]
    (is (= [["live" 2] ["live" 1]] @calls))
    (is (= 1 (get-in suppressed [:model :instances "live" :fault :effect-version])))
    (is (= 2 (get-in suppressed [:model :instances "live" :reload-fault :effect-version])))
    (is (= 2 (count (:fault-events failed))))
    (is (empty? (:fault-events suppressed)))))

(deftest faulted-timed-and-releasing-instances-still-expire
  (doseq [instance [(fixture/instance "shot" :duration-ms 20)
                    (fixture/instance "tail" :phase :releasing :release-at-ms 0 :release-duration-ms 20)]]
    (let [failed (invoke (fixture/model instance) 10 (fn [_] (fn [_] (throw (ex-info "Bad" {})))))
          done (invoke (:model failed) 20 (fn [_] (throw (AssertionError. "Expired code compiled"))))]
      (is (empty? (get-in done [:model :instances])))
      (is (= :instance/finished (-> done :intents last :type))))))

(deftest explicit-retry-is-idempotent-command-and-recovers-same-version
  (let [show (control/new-show (fixture/model (fixture/instance "live")))
        failed (invoke show 10 (fn [_] (fn [_] (throw (ex-info "Temporary" {})))))
        command {:op :instance/retry :instance-id "live" :command-id "retry" :source :test
                 :epoch (:epoch show) :show-id (:show-id show)}
        retry (control/apply-command (:model failed) command)
        duplicate (control/apply-command (:model retry) command)
        recovered (invoke (:model duplicate) 20 fixture/compiler)]
    (is (= :accepted (get-in retry [:ack :status])))
    (is (= (:model retry) (:model duplicate)))
    (is (= {:frames 1} (get-in recovered [:model :instances "live" :state])))
    (is (= [:effect/recovered] (mapv :type (:fault-events recovered))))))

(deftest cancellation-and-vm-failures-never-become-user-faults
  (doseq [error [(InterruptedException. "stop") (java.util.concurrent.CancellationException. "cancel")
                 (OutOfMemoryError. "test only") (ThreadDeath.)
                 (ex-info "wrapped stop" {} (InterruptedException. "stop"))]]
    (is (thrown? Throwable (invoke (fixture/model (fixture/instance "a")) 10 (fn [_] (throw error))))))
  (is (thrown? clojure.lang.ExceptionInfo
               (engine/advance (fixture/model (fixture/instance "a")) {:time-ms 10} fixture/compiler
                               (fn [_ _] [])))))

(deftest an-unsuccessful-explicit-retry-does-not-report-recovery-next-frame
  (let [compile (fn [_] (fn [_] (throw (ex-info "Still bad" {}))))
        failed (invoke (control/new-show (fixture/model (fixture/instance "live"))) 1 compile)
        retry (:model (control/apply-command (:model failed)
                                             {:op :instance/retry :instance-id "live" :command-id "retry"
                                              :source :test :show-id "test-show" :epoch 3}))
        failed-again (invoke retry 2 compile)
        held (invoke (:model failed-again) 3 compile)]
    (is (= [:effect/failed] (mapv :type (:fault-events failed-again))))
    (is (empty? (:fault-events held)))
    (is (get-in held [:model :instances "live" :fault]))
    (is (nil? (get-in held [:model :instances "live" :retry-fault])))))

(deftest renderer-rejection-does-not-repeat-healthy-evaluation
  (let [calls (atom []) compile (calls-compiler calls (fn [d c] (update ((fixture/compiler d) c) :intents conj :spark)))
        show (fixture/model (fixture/instance "bad") (fixture/instance "good" :order 1))
        evaluated (invoke show 10 compile)
        error (ex-info "Nonfinite aim" {:effect-source {:instance-id "bad" :effect-version 1}})
        isolated (engine/reject-output evaluated error)]
    (is (= [["bad" 1] ["good" 1]] @calls))
    (is (= ["good"] (mapv :source (:assignments isolated))))
    (is (= ["good"] (into [] (comp (filter #(= :spark (:intent %))) (map #(get-in % [:source :instance-id])))
                           (:intent-emissions isolated))))
    (is (= (:intents isolated) (mapv :intent (:intent-emissions isolated))))
    (is (= {:frames 0} (get-in isolated [:model :instances "bad" :state])))
    (is (= {:frames 1} (get-in isolated [:model :instances "good" :state])))
    (is (= :output (get-in isolated [:model :instances "bad" :fault :stage])))
    (is (thrown? clojure.lang.ExceptionInfo (engine/reject-output isolated error)))))

(deftest threaded-failures-preserve-semantic-order-and-state
  (let [show (fixture/model (fixture/instance "bad" :order 0)
                            (fixture/instance "good" :order 1))
        compile (fn [d] (fn [c] (if (= "bad" (get-in c [:instance :id]))
                                 (throw (ex-info "broken" {})) ((fixture/compiler d) c))))]
    (with-open [pool (executor/create {:workers 2 :queue-size 2 :timeout-ms 1000})]
      (let [serial (invoke show 10 compile)
            parallel (engine/advance show {:time-ms 10} compile (executor/mapper pool))]
        (is (= serial parallel))
        (is (= (:assignments serial) (:assignments parallel)))
        (is (= (mapv :state (vals (get-in serial [:model :instances])))
               (mapv :state (vals (get-in parallel [:model :instances])))))
        (is (= (mapv #(select-keys % [:type :instance-id :stage]) (:fault-events serial))
               (mapv #(select-keys % [:type :instance-id :stage]) (:fault-events parallel))))))))

(deftest fault-history-is-bounded-and-recordings-replay-across-worker-schedules
  (let [compile (fn [_] (fn [_] (throw (ex-info "Deterministic authored fault" {:path [:outputs 0]}))))
        show (control/new-show (fixture/model (fixture/instance "broken")))
        recorded (replay/record show [{:kind :frame :frame {:time-ms 10}}] compile)
        many (reduce (fn [model n]
                       (let [retried (:model (control/apply-command
                                              model {:op :instance/retry :instance-id "broken"
                                                     :show-id (:show-id model) :epoch (:epoch model)
                                                     :source :test :command-id (str "retry-" n)}))]
                         (:model (invoke retried (inc n) compile)))) show (range 100))]
    (is (= 64 (count (get-in many [:variables :runtime :events]))))
    (is (= 100 (get-in many [:variables :runtime :event-sequence])))
    (is (= 37 (get-in many [:variables :runtime :events 0 :sequence])))
    (with-open [pool (executor/create {:workers 2 :queue-size 2 :timeout-ms 1000})]
      (is (= 1 (:verified-steps (replay/replay (:recording recorded) compile {:map-work (executor/mapper pool)})))))))

(deftest retrying-a-candidate-that-still-fails-preparation-keeps-its-fault
  (let [model (-> (control/new-show (fixture/model (fixture/instance "live" :reload-policy :preserve-state)))
                  (assoc-in [:registry :effects :pulse :version] 2)
                  (assoc-in [:registry :effects :pulse :params :level] {:type :integer :default nil}))
        failed (invoke model 10 fixture/compiler)
        retry (:model (control/apply-command (:model failed)
                         {:op :instance/retry :instance-id "live" :command-id "retry-preparation"
                          :source :test :show-id (:show-id model) :epoch (:epoch model)}))
        again (invoke retry 20 fixture/compiler)]
    (is (= [:effect/reload-failed] (mapv :type (:fault-events failed))))
    (is (= [:effect/reload-failed] (mapv :type (:fault-events again))))
    (is (= 1 (get-in again [:model :instances "live" :effect-version])))))

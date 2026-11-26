(ns afterglow.runtime.reload-fallback-test
  "The ::engine/reload-fallback frame input: a frame whose inputs already follow
  a hot-reload candidate reads one whole input set, the frame's own when every
  candidate is accepted and the fallback when any is rejected."
  (:require [afterglow.control.model :as control]
            [afterglow.runtime.engine :as engine]
            [afterglow.runtime.executor :as executor]
            [clojure.test :refer [deftest is testing]]))

(def pulse
  {:id :pulse :version 1 :params {:level {:type :number :default 0.5}}})

(def wash
  {:id :wash :version 1 :params {:level {:type :number :default 0.25}}})

(defn- instance [id definition & overrides]
  (merge {:id id :cue-id (keyword id) :effect-id (:id definition) :effect-version (:version definition)
          :definition definition :params {:level 0.75} :state {:frames 0}
          :started-at-ms 0 :priority 0 :order 0 :phase :running
          :reload-policy :pinned :release-duration-ms 0}
         (apply hash-map overrides)))

(defn- model [effects & instances]
  {:show-id "fallback-show" :epoch 2 :revision 5 :time-ms 0
   :registry {:effects (merge {:pulse pulse :wash wash} effects) :cues {} :fixtures {}}
   :instances (into {} (map (juxt :id identity) instances))
   :variables {} :master 1.0 :blackout? false
   :transport {:bpm 120 :playing? true}})

(defn- step
  "A step that writes the frame's :inputs label and its :gain for this instance."
  [calls broken? definition]
  (fn [context]
    (let [id (get-in context [:instance :id])]
      (swap! calls conj [id (:version definition) (get-in context [:frame :inputs])])
      (when (broken? id (:version definition)) (throw (ex-info "Candidate cannot evaluate" {:path [:outputs 0]})))
      (-> context
          (update-in [:state :frames] (fnil inc 0))
          (update :assignments conj {:target-id (keyword id) :attribute :dimmer :blend :replace
                                     :value (* (get-in context [:frame :gain id] 1.0) (get-in context [:instance :params :level]))
                                     :inputs (get-in context [:frame :inputs])
                                     :private-fallback? (contains? (:frame context) ::engine/reload-fallback)
                                     :definition-version (:version definition)})
          (update :intents conj {:type :spark :instance-id id})))))

(defn- compiler
  ([calls] (compiler calls (constantly false)))
  ([calls broken?] (compiler calls broken? {}))
  ([calls broken? {:keys [uncompilable migrations]}]
   (fn [definition]
     (when (= uncompilable [(:id definition) (:version definition)])
       (throw (ex-info "Candidate cannot compile" {})))
     (cond-> (step calls broken? definition)
       (get migrations [(:id definition) (:version definition)])
       (engine/with-state-migration (get migrations [(:id definition) (:version definition)]))))))

(def own-frame {:time-ms 10 :inputs :candidate :gain {"other" 0.5}})

(def fallback {:inputs :last-good :gain {"other" 0.25}})

(def frame (assoc own-frame ::engine/reload-fallback fallback))

(defn- counted
  "A serial mapper that counts its mapping calls."
  [mappings]
  (fn [f jobs] (swap! mappings inc) (mapv f jobs)))

(defn- candidate-show
  ([policy] (candidate-show policy (assoc pulse :version 2)))
  ([policy candidate]
   (model {:pulse candidate}
          (instance "owner" pulse :reload-policy policy :state {:frames 4})
          (instance "other" wash :order 1 :state {:frames 7}))))

(defn- comparable
  "The parts of a result a renderer and the next frame read, without fault records."
  [result]
  {:assignments (:assignments result)
   :contributions (:contributions result)
   :instances (update-vals (get-in result [:model :instances])
                           #(dissoc % :reload-fault :definition :effect-version))})

(deftest accepted-candidates-read-the-frame-inputs-and-evaluate-everything-once
  (doseq [policy [:preserve-state :restart :migrate]]
    (testing (str policy)
      (let [calls (atom []) mappings (atom 0)
            compile (compiler calls (constantly false) {:migrations {[:pulse 2] (fn [state & _] (assoc state :migrated true))}})
            result (engine/advance (candidate-show policy) frame compile (counted mappings))
            plain (engine/advance (candidate-show policy) own-frame (compiler (atom []) (constantly false)
                                                                           {:migrations {[:pulse 2] (fn [state & _] (assoc state :migrated true))}}))]
        (is (= :frame (:reload-inputs result)))
        (is (= #{["owner" 2 :candidate] ["other" 1 :candidate]} (set @calls)))
        (is (= 2 (count @calls)) "No step runs twice")
        (is (= 2 @mappings) "Candidates first, then the other instances")
        (is (= 2 (get-in result [:model :instances "owner" :effect-version])))
        (is (= [:candidate :candidate] (mapv :inputs (:assignments result))))
        (is (= (dissoc result ::engine/evaluation :reload-inputs) (dissoc plain ::engine/evaluation))
            "An accepted frame is the frame the engine renders without a fallback")
        (is (not (contains? plain :reload-inputs)))))))

(deftest a-rejected-candidate-evaluates-the-whole-frame-on-the-fallback-inputs
  (doseq [policy [:preserve-state :restart :migrate]
          stage [:reload :compile :migrate :evaluate]
          :when (or (not= :migrate stage) (= :migrate policy))]
    (testing (str policy " rejected at " stage)
      (let [calls (atom []) mappings (atom 0)
            candidate (cond-> (assoc pulse :version 2)
                        (= :reload stage) (assoc-in [:params :level] {:type :integer :default 1}))
            options {:uncompilable (when (= :compile stage) [:pulse 2])
                     :migrations (when (= :migrate policy)
                                   {[:pulse 2] (if (= :migrate stage)
                                                 (fn [& _] (throw (ex-info "Unmigratable state" {})))
                                                 (fn [state & _] state))})}
            broken? (fn [id version] (and (= :evaluate stage) (= ["owner" 2] [id version])))
            result (engine/advance (candidate-show policy candidate) frame (compiler calls broken? options) (counted mappings))
            ;; The twin never had the candidate in its registry and was given the fallback inputs.
            twin (engine/advance (model {} (instance "owner" pulse :reload-policy policy :state {:frames 4})
                                        (instance "other" wash :order 1 :state {:frames 7}))
                                 (merge own-frame fallback) (compiler (atom [])))
            owner (get-in result [:model :instances "owner"])]
        (is (= :fallback (:reload-inputs result)))
        (is (= [1 stage 2] [(:effect-version owner) (get-in owner [:reload-fault :stage])
                            (get-in owner [:reload-fault :effect-version])]))
        (is (nil? (:fault owner)))
        (is (= [:effect/reload-failed] (mapv :type (:fault-events result))))
        (is (= (comparable twin) (comparable result)) "Output and state are those of a show that never saw the candidate")
        (is (= [:last-good :last-good] (mapv :inputs (:assignments result))))
        (is (= [["other" 1 :last-good]] (filterv #(= "other" (first %)) @calls))
            "A healthy instance evaluates once, after the candidates are decided")
        (is (= (if (= :evaluate stage) [["owner" 2 :candidate] ["owner" 1 :last-good]] [["owner" 1 :last-good]])
               (filterv #(= "owner" (first %)) @calls)))
        (is (= (if (= :reload stage) 1 2) @mappings) "Preparation rejects before any candidate is attempted")))))

(deftest a-rejection-defers-the-accepted-candidates-of-that-frame-without-a-fault
  (doseq [policy [:preserve-state :restart :migrate]]
    (testing (str policy)
      (let [calls (atom []) migrated (atom 0)
            broken? (fn [id version] (= ["bad" 2] [id version]))
            options {:migrations {[:pulse 2] (fn [state & _] (swap! migrated inc) (assoc state :migrated true))}}
            compile (compiler calls broken? options)
            show (model {:pulse (assoc pulse :version 2)}
                        (instance "bad" pulse :reload-policy policy)
                        (instance "good" pulse :reload-policy policy :order 1 :state {:frames 3})
                        (instance "other" wash :order 2))
            deferred (engine/advance show frame compile)
            good (get-in deferred [:model :instances "good"])
            adopted (engine/advance (:model deferred) (assoc frame :time-ms 20) compile)]
        (is (= :fallback (:reload-inputs deferred)))
        (is (= [1 nil nil {:frames 4} 0] [(:effect-version good) (:reload-fault good) (:fault good) (:state good)
                                          (:started-at-ms good)])
            "The accepted candidate's attempt is discarded: no state, restart or migration is committed")
        (is (= [1 1 1] (mapv :definition-version (:assignments deferred))))
        (is (= ["bad"] (mapv :instance-id (:fault-events deferred))))
        (is (not-any? #(= :effect/reloaded (:type %)) (:intents deferred)))
        (is (= 3 (count (filter #(= :spark (:type %)) (:intents deferred)))) "The discarded attempt publishes no intents")
        (testing "the next frame has no rejected candidate left and adopts it"
          (is (= :frame (:reload-inputs adopted)))
          (is (= [2 nil] ((juxt :effect-version :reload-fault) (get-in adopted [:model :instances "good"]))))
          (is (= [1 2] ((juxt :effect-version (comp :effect-version :reload-fault)) (get-in adopted [:model :instances "bad"]))))
          (is (= ["good"] (into [] (comp (filter #(= :effect/reloaded (:type %))) (map :instance-id)) (:intents adopted))))
          (is (= [["bad" 1 :candidate] ["good" 2 :candidate] ["other" 1 :candidate]]
                 (sort (filterv #(= :candidate (peek %)) (drop 5 @calls)))))
          (when (= :migrate policy)
            (is (= {:frames 5 :migrated true} (get-in adopted [:model :instances "good" :state])))
            (is (= 3 @migrated) "The pure migration ran for both discarded attempts and for the adopted one")))))))

(deftest fallback-opacity-factors-and-priority-overrides-replace-the-frames-own
  (let [calls (atom [])
        show (model {:pulse (assoc pulse :version 2)}
                    (instance "owner" pulse :reload-policy :preserve-state)
                    (instance "other" wash :order 1))
        frame (assoc own-frame
                     ::engine/priority-overrides {"owner" 5}
                     ::engine/opacity-factors {"other" 0.5}
                     ::engine/reload-fallback (assoc fallback ::engine/priority-overrides {} ::engine/opacity-factors {"other" 0.25}))
        accepted (engine/advance show frame (compiler calls))
        rejected (engine/advance show frame (compiler calls (fn [id version] (= ["owner" 2] [id version]))))
        opacity #(some (fn [assignment] (when (= :other (:target-id assignment)) (:opacity assignment 1.0))) (:assignments %))]
    (is (= [:other :owner] (mapv :target-id (:assignments accepted))) "The frame's override lifts the candidate above the wash")
    (is (= [:owner :other] (mapv :target-id (:assignments rejected))) "The fallback keeps launch order")
    (is (= [0.5 0.25] [(opacity accepted) (opacity rejected)]))
    (is (not-any? :private-fallback? (mapcat :assignments [accepted rejected]))
        "The fallback map itself stays outside every effect context")))

(deftest a-renderer-rejected-candidate-evaluates-the-frame-again-on-the-fallback-inputs
  (let [calls (atom [])
        show (candidate-show :preserve-state)
        error (ex-info "Nonfinite aim" {:effect-source {:instance-id "owner" :effect-version 2}})
        accepted (engine/advance show frame (compiler calls))
        resolved (engine/reject-output accepted error)
        twin (engine/advance (model {} (instance "owner" pulse :reload-policy :preserve-state :state {:frames 4})
                                    (instance "other" wash :order 1 :state {:frames 7}))
                             (merge own-frame fallback) (compiler (atom [])))
        owner (get-in resolved [:model :instances "owner"])]
    (is (= [:frame :fallback] (mapv :reload-inputs [accepted resolved])))
    (is (= [1 :output 2] [(:effect-version owner) (get-in owner [:reload-fault :stage])
                          (get-in owner [:reload-fault :effect-version])]))
    (is (= (comparable twin) (comparable resolved)) "The last good revision renders this frame")
    (is (= [:effect/reload-failed] (mapv :type (:fault-events resolved))))
    (is (= 1 (get-in resolved [:model :variables :runtime :event-sequence])))
    (is (= [["owner" 2 :candidate] ["other" 1 :candidate] ["owner" 1 :last-good] ["other" 1 :last-good]]
           (sort-by #(.indexOf [:candidate :last-good] (peek %)) @calls)))
    (testing "the last good revision's own output can still be rejected once"
      (let [again (engine/reject-output resolved (ex-info "Nonfinite aim" {:effect-source {:instance-id "owner" :effect-version 1}}))]
        (is (= :output (get-in again [:model :instances "owner" :fault :stage])))
        (is (= [:other] (mapv :target-id (:assignments again))))
        (is (thrown? clojure.lang.ExceptionInfo (engine/reject-output again error)))))
    (testing "without a fallback the candidate is silenced and nothing runs again"
      (reset! calls [])
      (let [plain (engine/advance show own-frame (compiler calls))
            silenced (engine/reject-output plain error)]
        (is (= 2 (count @calls)))
        (is (= [:other] (mapv :target-id (:assignments silenced))))
        (is (= :output (get-in silenced [:model :instances "owner" :reload-fault :stage])))
        (is (not (contains? silenced :reload-inputs)))))
    (testing "a rejected healthy output keeps the pending fallback for a later candidate rejection"
      (let [first-rejection (engine/reject-output accepted (ex-info "Bad wash" {:effect-source {:instance-id "other" :effect-version 1}}))
            both (engine/reject-output first-rejection error)]
        (is (= [:frame :fallback] (mapv :reload-inputs [first-rejection both])))
        (is (= [:owner] (mapv :target-id (:assignments first-rejection))))
        (is (= [:owner :other] (mapv :target-id (:assignments both))))
        (is (= [1 1] (mapv :definition-version (:assignments both))))))))

(deftest an-empty-fallback-keeps-the-single-candidate-result
  (doseq [policy [:preserve-state :restart :migrate]
          stage [:accepted :reload :compile :evaluate]]
    (testing (str policy " " stage)
      (let [candidate (cond-> (assoc pulse :version 2)
                        (= :reload stage) (assoc-in [:params :level] {:type :integer :default 1}))
            options {:uncompilable (when (= :compile stage) [:pulse 2])
                     :migrations {[:pulse 2] (fn [state & _] (assoc state :migrated true))}}
            broken? (fn [id version] (and (= :evaluate stage) (= ["owner" 2] [id version])))
            run #(dissoc (engine/advance (candidate-show policy candidate) % (compiler (atom []) broken? options))
                         ::engine/evaluation :reload-inputs)]
        (is (= (run own-frame) (run (assoc own-frame ::engine/reload-fallback {})))))))
  (testing "a retried last-good revision that runs again beside a rejected candidate reports no recovery"
    (let [broken (atom #{1 2})
          compile (fn [definition]
                    (fn [context]
                      (when (@broken (:version definition)) (throw (ex-info "Broken revision" {})))
                      (update-in context [:state :frames] (fnil inc 0))))
          show (control/new-show (model {} (instance "live" pulse :reload-policy :preserve-state)))
          failed (:model (engine/advance show {:time-ms 10} compile))
          retried (:model (control/apply-command (assoc-in failed [:registry :effects :pulse :version] 2)
                                                 {:op :instance/retry :instance-id "live" :command-id "retry"
                                                  :source :test :show-id (:show-id show) :epoch (:epoch show)}))
          _ (reset! broken #{2})
          plain (engine/advance retried {:time-ms 20} compile)
          with-fallback (engine/advance retried {:time-ms 20 ::engine/reload-fallback {}} compile)]
      (is (= [:effect/reload-failed] (mapv :type (:fault-events plain))))
      (is (= (dissoc plain ::engine/evaluation) (dissoc with-fallback ::engine/evaluation :reload-inputs))))))

(deftest frames-without-candidates-make-one-mapping-call
  (let [mappings (atom 0)
        show (model {} (instance "owner" pulse :reload-policy :preserve-state) (instance "other" wash :order 1))
        result (engine/advance show frame (compiler (atom [])) (counted mappings))]
    (is (= 1 @mappings))
    (is (= :frame (:reload-inputs result)))
    (is (= [:candidate :candidate] (mapv :inputs (:assignments result))))
    (testing "and so do candidate frames that supply no fallback"
      (reset! mappings 0)
      (let [plain (engine/advance (candidate-show :preserve-state) own-frame (compiler (atom [])) (counted mappings))]
        (is (= 1 @mappings))
        (is (not (contains? plain :reload-inputs)))))))

(deftest paused-and-pinned-instances-are-not-candidates
  (let [calls (atom [])
        show (model {:pulse (assoc pulse :version 2)}
                    (instance "pinned" pulse)
                    (instance "paused" pulse :reload-policy :preserve-state :order 1
                              :system {:paused? true :paused-clock {:time-ms 0 :beat 0}}))
        result (engine/advance show frame (compiler calls (fn [_ version] (= 2 version))))]
    (is (= :frame (:reload-inputs result)))
    (is (= [1 1] (mapv :definition-version (:assignments result))))
    (is (empty? (:fault-events result)))))

(deftest serial-and-two-worker-evaluation-agree
  (doseq [broken? [(constantly false) (fn [id version] (= ["bad" 2] [id version]))]]
    (let [show (model {:pulse (assoc pulse :version 2)}
                      (instance "bad" pulse :reload-policy :preserve-state)
                      (instance "good" pulse :reload-policy :restart :order 1)
                      (instance "other" wash :order 2)
                      (instance "more" wash :order 3))
          run (fn [mapper] (let [result (engine/advance show frame (compiler (atom []) broken?) mapper)]
                             [(dissoc result ::engine/evaluation)
                              (dissoc (engine/advance (:model result) (assoc frame :time-ms 20)
                                                      (compiler (atom []) broken?) mapper)
                                      ::engine/evaluation)]))]
      (with-open [pool (executor/create {:workers 2 :queue-size 2 :timeout-ms 1000})]
        (is (= (run mapv) (run (executor/mapper pool))))))))

(deftest fallback-inputs-are-validated-with-the-frame
  (let [show (candidate-show :preserve-state)
        code (fn [fallback]
               (try (engine/advance show (assoc own-frame ::engine/reload-fallback fallback) (compiler (atom [])))
                    (catch clojure.lang.ExceptionInfo error (:type (ex-data error)))))]
    (doseq [invalid [[] nil {:time-ms 20} {:delta-ms 1} {:epoch 2} {:show-id "fallback-show"}
                     {::engine/reload-fallback {}}]]
      (is (= ::engine/invalid-reload-fallback (code invalid)) (pr-str invalid)))
    (is (= ::engine/invalid-opacity-factors (code {::engine/opacity-factors {"missing" 1}})))
    (is (= ::engine/invalid-priority-overrides (code {::engine/priority-overrides {"owner" ##NaN}})))
    (is (map? (code {})))))

(ns afterglow.runtime.state-migration-test
  "The :migrate reload policy through engine/advance and real control commands."
  (:require [afterglow.runtime.engine :as engine]
            [afterglow.runtime.executor :as executor]
            [afterglow.control.model :as control]
            [clojure.test :refer [deftest is testing]]))

(def definition
  {:id :pulse :version 1 :params {:level {:type :number :default 0.5}}})

(def other
  {:id :other :version 1 :params {:level {:type :number :default 0.25}}})

(defn- instance [id & overrides]
  (merge {:id id :cue-id (keyword id) :effect-id :pulse :effect-version 1
          :definition definition :params {:level 0.75} :state {:frames 0}
          :started-at-ms 0 :priority 0 :order 0 :phase :running
          :reload-policy :pinned :release-duration-ms 0}
         (apply hash-map overrides)))

(defn- model [registry & instances]
  {:show-id "migration-show" :epoch 4 :revision 9 :time-ms 0
   :registry (merge {:effects {:pulse definition :other other} :cues {} :fixtures {}} registry)
   :instances (into {} (map (juxt :id identity) instances))
   :variables {} :master 1.0 :blackout? false
   :transport {:bpm 120 :playing? true}})

(defn- step [definition]
  (fn [context]
    (-> context
        (update-in [:state :frames] (fnil inc 0))
        (update :assignments conj {:target-id (keyword (get-in context [:instance :id]))
                                   :attribute :dimmer :blend :replace
                                   :value (get-in context [:instance :params :level])
                                   :definition-version (:version definition)}))))

(defn- compiler
  "Attach a migration to the compiled step of each definition version that has one."
  [migrations]
  (fn [definition]
    (cond-> (step definition)
      (get migrations [(:id definition) (:version definition)])
      (engine/with-state-migration (get migrations [(:id definition) (:version definition)])))))

(defn- frames->ticks [state from to context]
  {:ticks (* 10 (:frames state)) :frames 0 :migrated [from to]
   :seen (select-keys context [:instance-id :cue-id :effect-id])
   :level (get-in context [:params :level])
   :from-definition (get-in context [:from-definition :version])
   :to-definition (get-in context [:to-definition :version])
   :frame (get-in context [:frame :number])})

(deftest accepted-migration-transforms-state-once-at-the-takeover-frame
  (let [calls (atom 0)
        migrate (fn [& args] (swap! calls inc) (apply frames->ticks args))
        v2 (assoc definition :version 2)
        show (model {:effects {:pulse v2 :other other}}
                    (instance "migrated" :reload-policy :migrate :state {:frames 5}))
        compile (compiler {[:pulse 2] migrate})
        first-frame (engine/advance show {:time-ms 10} compile)
        migrated (get-in first-frame [:model :instances "migrated"])
        second-frame (engine/advance (:model first-frame) {:time-ms 20} compile)]
    (is (= 2 (:effect-version migrated)))
    (is (= {:ticks 50 :frames 1 :migrated [1 2] :level 0.75 :from-definition 1 :to-definition 2 :frame 1
            :seen {:instance-id "migrated" :cue-id :migrated :effect-id :pulse}}
           (:state migrated))
        "The step first sees migrated state; retained params reach the migration context")
    (is (= [2] (mapv :definition-version (:assignments first-frame))))
    (is (= [{:type :effect/reloaded :instance-id "migrated" :from-version 1 :to-version 2 :policy :migrate}]
           (:intents first-frame)))
    (is (nil? (:reload-fault migrated)))
    (is (= 2 (get-in second-frame [:model :instances "migrated" :state :frames])))
    (is (= 1 @calls) "A migration never runs again once its definition has taken over")
    (is (empty? (:intents second-frame)))))

(defn- broken-show [registry]
  (model registry
         (instance "a" :order 0 :state {:frames 3})
         (instance "broken" :order 1 :reload-policy :migrate :state {:frames 7})
         (instance "c" :order 2 :effect-id :other :definition other :effect-version 1
                   :reload-policy :preserve-state :params {:level 0.25} :state {:frames 1})))

(defn- throwing-migration [calls]
  (fn [state _ _ _]
    (swap! calls inc)
    (throw (ex-info "Unknown legacy counter" {:path [:state-migration :steps 0] :state-keys (vec (keys state))}))))

(deftest throwing-migration-keeps-the-last-good-revision-while-other-cues-render-identically
  (let [calls (atom 0)
        v2 (assoc definition :version 2)
        compile (compiler {[:pulse 2] (throwing-migration calls)})
        unchanged (engine/advance (broken-show {}) {:time-ms 10} compile)
        failed (engine/advance (broken-show {:effects {:pulse v2 :other other}}) {:time-ms 10} compile)
        broken (get-in failed [:model :instances "broken"])
        fault (:reload-fault broken)]
    (is (= (:assignments unchanged) (:assignments failed))
        "The broken instance renders its captured revision and its neighbours are unaffected")
    (is (= (:contributions unchanged) (:contributions failed)))
    (is (= ["a" "broken" "c"] (mapv (comp name :target-id) (:assignments failed))) "Launch order is preserved")
    (is (= 1 (:effect-version broken)))
    (is (= {:frames 8} (:state broken)) "Last good state advances under the last good definition")
    (is (= (get-in unchanged [:model :instances "a"]) (get-in failed [:model :instances "a"])))
    (is (= (get-in unchanged [:model :instances "c"]) (get-in failed [:model :instances "c"])))
    (is (= {:stage :migrate :effect-version 2 :from-version 1 :instance-id "broken" :cue-id :broken
            :effect-id :pulse :epoch 4 :show-id "migration-show" :number 1 :time-ms 10}
           (select-keys fault [:stage :effect-version :from-version :instance-id :cue-id :effect-id
                               :epoch :show-id :number :time-ms])))
    (is (= "Unknown legacy counter" (:message fault)))
    (is (= [{:type ::engine/state-migration-failed :path [:state-migration]}
            {:path [:state-migration :steps 0]}]
           (mapv :location (:causes fault)))
        "The fault keeps the engine boundary and the authored migration path")
    (is (= [:effect/reload-failed] (mapv :type (:fault-events failed))))
    (is (= [fault] (mapv #(dissoc % :type :sequence) (get-in failed [:model :variables :runtime :events]))))
    (let [next-frame (engine/advance (:model failed) {:time-ms 20} compile)]
      (is (= 1 @calls) "A quarantined migration is not retried every frame")
      (is (empty? (:fault-events next-frame)))
      (is (= {:frames 9} (get-in next-frame [:model :instances "broken" :state])))
      (testing "a newer definition with a working migration recovers from the last good state"
        (let [v3 (assoc definition :version 3)
              compile (compiler {[:pulse 2] (throwing-migration calls) [:pulse 3] frames->ticks})
              recovered (engine/advance (assoc-in (:model next-frame) [:registry :effects :pulse] v3)
                                        {:time-ms 30} compile)
              instance (get-in recovered [:model :instances "broken"])]
          (is (= 3 (:effect-version instance)))
          (is (= [1 3] (get-in instance [:state :migrated])))
          (is (= 90 (get-in instance [:state :ticks])))
          (is (nil? (:reload-fault instance)))
          (is (= [:effect/recovered] (mapv :type (:fault-events recovered)))))))))

(deftest missing-or-invalid-migrations-are-reload-faults
  (doseq [[label migrations message]
          [["no migration" {} "The new definition declares no state migration"]
           ["function result" {[:pulse 2] (fn [_ _ _ _] inc)} "A state migration must return state data, not a function"]]]
    (testing label
      (let [show (model {:effects {:pulse (assoc definition :version 2) :other other}}
                        (instance "x" :reload-policy :migrate))
            result (engine/advance show {:time-ms 5} (compiler migrations))
            instance (get-in result [:model :instances "x"])]
        (is (= 1 (:effect-version instance)))
        (is (= :migrate (get-in instance [:reload-fault :stage])))
        (is (= message (get-in instance [:reload-fault :message])))
        (is (= [0.75] (mapv :value (:assignments result))))))))

(deftest parallel-workers-merge-migrations-in-launch-order
  (let [v2 (assoc definition :version 2)
        show (model {:effects {:pulse v2 :other other}}
                    (instance "first" :order 0 :reload-policy :migrate :state {:frames 1})
                    (instance "second" :order 1 :reload-policy :migrate :state {:frames 2})
                    (instance "third" :order 2 :reload-policy :migrate :state {:frames 3}))
        compile (compiler {[:pulse 2] (fn [state from to context]
                                        (when (= "second" (:instance-id context))
                                          (throw (ex-info "second fails" {:path [:state-migration]})))
                                        (frames->ticks state from to context))})
        serial (engine/advance show {:time-ms 10} compile)]
    (with-open [^java.io.Closeable pool (executor/create {:workers 2 :queue-size 3 :timeout-ms 1000})]
      (let [parallel (engine/advance show {:time-ms 10} compile (executor/mapper pool))]
        (is (= (dissoc serial ::engine/evaluation) (dissoc parallel ::engine/evaluation)))
        (is (= [2 1 2] (mapv :definition-version (:assignments parallel))))
        (is (= ["first" "second" "third"] (mapv (comp name :target-id) (:assignments parallel))))))))

(deftest interrupts-and-vm-errors-propagate-from-migrations
  (doseq [error [(InterruptedException. "stop") (StackOverflowError.)
                 (ex-info "wrapped" {} (InterruptedException. "stop"))]]
    (let [show (model {:effects {:pulse (assoc definition :version 2) :other other}}
                      (instance "x" :reload-policy :migrate))
          thrown (try (engine/advance show {:time-ms 5} (compiler {[:pulse 2] (fn [& _] (throw error))}))
                      ::returned
                      (catch Throwable caught caught))]
      (is (identical? error thrown)))))

(deftest attaching-a-non-function-is-rejected
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"must be a function"
                        (engine/with-state-migration (step definition) {:op :rename}))))

(defn- command! [show payload]
  (control/apply-command show (merge {:command-id (str (:revision show) (:op payload))
                                      :show-id (:show-id show) :epoch (:epoch show)
                                      :time-ms (:time-ms show) :source {:adapter :test}}
                                     payload)))

(deftest cues-and-launches-validate-the-policy-when-published
  (let [show (control/new-show {:registry {:effects {:pulse definition}}})
        rejected (command! show {:op :cue/put :cue {:id :bad :effect-id :pulse :reload-policy :migrate-later}})
        accepted (command! show {:op :cue/put :cue {:id :good :effect-id :pulse :reload-policy :migrate}})
        launched (command! (:model accepted) {:op :cue/launch :cue-id :good})
        bad-launch (command! (:model accepted) {:op :cue/launch :cue-id :good :launch {:reload-policy :sometimes}})
        id (get-in launched [:ack :instance-id])
        v2 (command! (:model launched) {:op :registry/publish :kind :effects :definition (assoc definition :version 2)})
        frame (engine/advance (:model v2) {:time-ms 0}
                              (compiler {[:pulse 2] (fn [state _ _ _] (assoc state :migrated? true))}))]
    (is (= :rejected (get-in rejected [:ack :status])))
    (is (= {:path [:reload-policy] :reload-policy :migrate-later} (get-in rejected [:ack :details])))
    (is (= :accepted (get-in launched [:ack :status])))
    (is (= :rejected (get-in bad-launch [:ack :status])))
    (is (= :migrate (get-in launched [:model :instances id :reload-policy])))
    (is (= {:migrated? true :frames 1} (get-in frame [:model :instances id :state])))))

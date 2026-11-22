(ns afterglow.runtime.engine-test
  (:require [afterglow.runtime.engine :as engine]
            [afterglow.runtime.reuse :as reuse]
            [afterglow.runtime.executor :as executor]
            [afterglow.control.model :as control]
            [clojure.test :refer [deftest is testing]]))

(def definition
  {:id :pulse :version 1 :params {:level {:type :number :default 0.5}}})

(defn instance
  [id & overrides]
  (merge {:id id :cue-id :pulse :effect-id :pulse :effect-version 1
          :definition definition :params {:level 0.75} :state {:frames 0}
          :started-at-ms 0 :priority 0 :order 0 :phase :running
          :reload-policy :pinned :release-duration-ms 0}
         (apply hash-map overrides)))

(defn model
  [& instances]
  {:show-id "test-show" :epoch 3 :revision 7 :time-ms 0
   :registry {:effects {:pulse definition} :cues {} :fixtures {}}
   :instances (into {} (map (juxt :id identity) instances))
   :variables {:global 1} :master 1.0 :blackout? false
   :transport {:bpm 120 :playing? true}})

(defn compiler
  [definition]
  (fn [context]
    (let [instance (:instance context)
          time-ms (get-in context [:frame :time-ms])
          release (if (= :releasing (:phase instance))
                    (- 1.0 (/ (- time-ms (:release-at-ms instance))
                              (:release-duration-ms instance)))
                    1.0)]
      (-> context
          (update-in [:state :frames] (fnil inc 0))
          (update :assignments conj {:target-id :pixel :attribute :dimmer
                                     :value (* release (get-in instance [:params :level]))
                                     :definition-version (:version definition)
                                     :source (:id instance) :blend :replace})))))

(defn musical-show []
  (control/new-show
   {:registry {:effects {:music {:id :music :version 1 :params {}
                                :duration {:bars 1} :release-duration {:beats 1/2}}}
               :cues {:music {:id :music :version 1 :effect-id :music}}}}))

(defn control! [show payload]
  (let [result (control/apply-command show (merge {:command-id (str (:revision show))
                                                  :show-id (:show-id show) :epoch (:epoch show)
                                                  :time-ms (:time-ms show) :source {:adapter :test}}
                                                 payload))]
    (is (= :accepted (get-in result [:ack :status])))
    (:model result)))

(defn at-beat [show milliseconds beat]
  (engine/advance (assoc-in show [:transport :beat] beat) {:time-ms milliseconds}
                  (fn [_] #(update % :intents conj {:seen-phase (get-in % [:instance :phase])}))))

(deftest musical-one-shots-and-fractional-release-follow-beats-through-tempo-and-pause
  (let [launched (control! (musical-show) {:op :cue/launch :cue-id :music :launch {:mode :one-shot}})
        first-frame (at-beat launched 500 1)
        paused (at-beat (assoc-in (:model first-frame) [:transport :playing?] false) 6000 1)
        running (at-beat (update (:model paused) :transport assoc :bpm 60 :playing? true) 8000 3.75)
        release (at-beat (:model running) 8500 4.25)
        instance (first (vals (get-in release [:model :instances])))
        done (at-beat (:model release) 9000 4.5)]
    (is (= :running (-> paused :intents first :seen-phase)))
    (is (= :running (-> running :intents first :seen-phase)))
    (is (= :releasing (:phase instance)))
    (is (== 4 (:release-at-beat instance)) "Late frames retain the exact beat boundary")
    (is (= 8250.0 (:release-at-ms instance)))
    (is (== 4 (get-in instance [:release-timer :started-at])))
    (is (empty? (get-in done [:model :instances])))))

(deftest musical-meter-is-captured-and-restart-resets-the-beat-anchor
  (let [initial (-> (musical-show)
                    (assoc-in [:transport :meter] {:beats-per-bar 3 :bars-per-phrase 2}))
        launched (control! initial {:op :cue/launch :cue-id :music
                                     :launch {:mode :one-shot :reload-policy :restart}})
        id (first (keys (:instances launched)))
        _ (is (= 3 (get-in launched [:instances id :duration-timer :duration :value])))
        new-version (-> launched
                        (assoc-in [:transport :meter] {:beats-per-bar 7 :bars-per-phrase 4})
                        (assoc-in [:registry :effects :music :version] 2))
        reloaded (at-beat new-version 1000 2)
        instance (get-in reloaded [:model :instances id])
        ended (control! (:model reloaded) {:op :instance/end :instance-id id})
        done (at-beat ended 1100 2.5)]
    (is (= 2 (:started-at-beat instance)))
    (is (= 2 (get-in instance [:duration-timer :started-at])))
    (is (= 3 (get-in instance [:duration-timer :duration :value])))
    (is (= 2 (get-in ended [:instances id :release-at-beat])))
    (is (empty? (get-in done [:model :instances])))))

(deftest captured-definitions-and-current-params
  (let [show (-> (model (instance "a"))
                 (assoc-in [:registry :effects :pulse :version] 2)
                 (assoc-in [:instances "a" :params :level] 0.4))
        result (engine/advance show {:epoch 3 :time-ms 20} compiler)]
    (is (= 1 (-> result :assignments first :definition-version)))
    (is (= 0.4 (-> result :assignments first :value)))
    (is (= {:frames 1} (get-in result [:model :instances "a" :state])))
    (is (= 1 (get-in result [:model :frame-number])))
    (is (= 7 (get-in result [:model :revision])))
    (is (= 20 (get-in result [:model :last-frame-time-ms])))
    (is (= {:frames 0} (get-in show [:instances "a" :state])))
    (is (= result (engine/advance show {:epoch 3 :time-ms 20} compiler)))))

(deftest explicit-snapshot-and-elapsed-frame-time
  (let [show (assoc (model (instance "a")) :time-ms 15 :last-frame-time-ms 10)
        result (engine/advance show {:time-ms 20 :variables {:wrong true}}
                               (fn [_] #(update % :intents conj (:frame %))))
        snapshot (first (:intents result))]
    (is (= 10 (:delta-ms snapshot)))
    (is (= {:global 1} (:variables snapshot)))
    (is (= 3 (:epoch snapshot)))
    (is (= "test-show" (:show-id snapshot)))))

(deftest timed-one-shot-and-release-tail
  (let [show (model (instance "shot" :mode :one-shot :duration-ms 100
                              :release-duration-ms 50))
        running (engine/advance show {:time-ms 99} compiler)
        releasing (engine/advance (:model running) {:time-ms 125} compiler)
        finished (engine/advance (:model releasing) {:time-ms 150} compiler)]
    (is (= :running (get-in running [:model :instances "shot" :phase])))
    (is (= :releasing (get-in releasing [:model :instances "shot" :phase])))
    (is (= 100 (get-in releasing [:model :instances "shot" :release-at-ms])))
    (is (= 0.375 (-> releasing :assignments first :value)))
    (is (empty? (get-in finished [:model :instances])))
    (is (= [] (:assignments finished)))
    (is (= :release-complete (-> finished :intents last :reason)))))

(deftest no-release-tail-stops-at-the-exact-deadline
  (let [show (model (instance "timed" :duration-ms 100))
        result (engine/advance show {:time-ms 100}
                               (fn [_] (throw (ex-info "Expired instances need no compile" {}))))]
    (is (= {} (get-in result [:model :instances])))
    (is (= [] (:assignments result)))))

(deftest manual-release-and-effect-owned-completion
  (let [show (model (instance "manual" :phase :releasing :release-at-ms 10
                              :release-duration-ms 100))
        result (engine/advance show {:time-ms 20}
                               (fn [definition]
                                 (comp #(assoc % :done? true) (compiler definition))))]
    (is (= 0.675 (-> result :assignments first :value)))
    (is (= {} (get-in result [:model :instances])))
    (is (= :effect-complete (-> result :intents last :reason)))))

(deftest reload-policies-are-explicit
  (let [new-definition (assoc definition :version 2 :initial-state {:frames 20}
                              :params {:level {:type :number :default 0.1}
                                       :speed {:type :number :default 2}})
        show (-> (model (instance "pinned" :order 0)
                        (instance "preserved" :order 1 :reload-policy :preserve-state
                                  :state {:frames 5})
                        (instance "restarted" :order 2 :reload-policy :restart
                                  :state {:frames 10}))
                 (assoc-in [:registry :effects :pulse] new-definition))
        result (engine/advance show {:time-ms 40} compiler)
        instances (get-in result [:model :instances])]
    (is (= [1 2 2] (mapv :definition-version (:assignments result))))
    (is (= {:frames 1} (get-in instances ["pinned" :state])))
    (is (= {:frames 6} (get-in instances ["preserved" :state])))
    (is (= {:frames 21} (get-in instances ["restarted" :state])))
    (is (= 0 (get-in instances ["preserved" :started-at-ms])))
    (is (= 40 (get-in instances ["restarted" :started-at-ms])))
    (is (= {:level 0.75 :speed 2} (get-in instances ["restarted" :params])))
    (is (= [:effect/reloaded :effect/reloaded] (mapv :type (:intents result))))
    (is (empty? (:intents (engine/advance (:model result) {:time-ms 41} compiler))))))

(deftest removed-registry-definition-does-not-orphan-an-instance
  (let [show (assoc-in (model (instance "a" :reload-policy :preserve-state))
                       [:registry :effects] {})]
    (is (= 1 (count (:assignments (engine/advance show {:time-ms 1} compiler)))))))

(deftest incompatible-reload-parameters-retain-the-captured-revision
  (let [show (-> (model (instance "a" :reload-policy :preserve-state))
                 (assoc-in [:registry :effects :pulse]
                           (assoc definition :version 2
                                  :params {:level {:type :boolean :default false}})))]
    (let [result (engine/advance show {:time-ms 10} compiler)]
      (is (= 1 (get-in result [:model :instances "a" :effect-version])))
      (is (= :reload (get-in result [:model :instances "a" :reload-fault :stage])))
      (is (= 0.75 (-> result :assignments first :value))))
    (is (= 1 (get-in show [:instances "a" :effect-version])))))

(deftest compile-shared-definitions-once-per-frame
  (let [compiled (atom [])
        show (model (instance "a") (instance "b" :order 1))]
    (engine/advance show {:time-ms 1}
                    (fn [definition] (swap! compiled conj definition) (compiler definition)))
    (is (= [definition] @compiled))))

(deftest effect-failures-preserve-input-and-isolate-attempts
  (let [show (model (instance "a") (instance "b" :order 1))]
    (let [result (engine/advance show {:time-ms 20} (fn [_] (throw (ex-info "Compile failed" {}))))]
      (is (empty? (:assignments result)))
      (is (= [:compile :compile] (mapv #(get-in % [:fault :stage]) (sort-by :id (vals (get-in result [:model :instances])))))))
    (let [result (engine/advance show {:time-ms 20}
                                 (fn [definition]
                                   (fn [context]
                                     (if (= "b" (get-in context [:instance :id]))
                                       (throw (ex-info "Step failed" {}))
                                       ((compiler definition) context)))))]
      (is (= ["a"] (mapv :source (:assignments result))))
      (is (= {:frames 0} (get-in result [:model :instances "b" :state]))))
    (is (= [{:frames 0} {:frames 0}] (mapv :state (sort-by :id (vals (:instances show))))))
    (is (= 0 (:time-ms show)))))

(deftest stale-epochs-and-time-are-rejected-before-compilation
  (let [show (assoc (model (instance "a")) :time-ms 10)
        never-compile (fn [_] (throw (AssertionError. "Compiled rejected frame")))]
    (doseq [[frame expected] [[{:time-ms 20 :epoch 2} ::engine/stale-epoch]
                              [{:time-ms 9} ::engine/stale-time]
                              [{:time-ms 20 :show-id "other"} ::engine/wrong-show]]]
      (is (= expected (try (engine/advance show frame never-compile)
                           (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))))))

(deftest threaded-evaluation-equals-serial-order-and-state
  (let [show (model (instance "high" :priority 2 :order 0)
                    (instance "later" :priority 0 :order 2)
                    (instance "early" :priority 0 :order 1))]
    (with-open [^java.io.Closeable pool (executor/create {:workers 2 :queue-size 2 :timeout-ms 1000})]
      (let [serial (engine/advance show {:time-ms 20} compiler)
            parallel (engine/advance show {:time-ms 20} compiler (executor/mapper pool))]
        (is (= serial parallel))
        (is (= ["early" "later" "high"] (mapv :source (:assignments parallel))))))))

(defn- command
  [show id op & fields]
  (control/apply-command show
                         (merge {:command-id id :source :runtime-test :op op
                                 :show-id (:show-id show) :epoch (:epoch show)}
                                (apply hash-map fields))))

(deftest real-control-commands-drive-lifecycle-params-reload-and-restart
  (let [effect (assoc definition :envelope {:release-ms 50})
        show (control/new-show {:show-id "integration"})
        published (command show :publish :registry/publish :kind :effects :definition effect)
        cued (command (:model published) :cue :cue/put
                       :cue {:id :pulse :effect-id :pulse :reload-policy :preserve-state})
        launched (command (:model cued) :launch :cue/launch :cue-id :pulse :time-ms 0
                           :launch {:mode :one-shot :duration-ms 100})
        id (get-in launched [:ack :instance-id])
        first-frame (engine/advance (:model launched) {:time-ms 10 :epoch 0} compiler)
        adjusted (command (:model first-frame) :adjust :param/set
                           :instance-id id :param :level :value 0.2)
        republished (command (:model adjusted) :republish :registry/publish :kind :effects
                              :definition (assoc effect :version 2))
        tail (engine/advance (:model republished) {:time-ms 125 :epoch 0} compiler)
        finished (engine/advance (:model tail) {:time-ms 150 :epoch 0} compiler)
        relaunched (command (:model finished) :relaunch :cue/launch :cue-id :pulse :time-ms 150)
        restarted (command (:model relaunched) :restart :show/restart :time-ms 151)]
    (doseq [result [published cued launched adjusted republished relaunched restarted]]
      (is (= :accepted (get-in result [:ack :status]))))
    (is (= 50 (get-in launched [:model :instances id :release-duration-ms]))
        "Control preserves the declarative envelope's release tail")
    (is (= 0.1 (-> tail :assignments first :value)))
    (is (= 2 (-> tail :assignments first :definition-version)))
    (is (= :effect/reloaded (-> tail :intents first :type)))
    (is (empty? (get-in finished [:model :instances])))
    (is (empty? (get-in restarted [:model :instances])))
    (is (= ::engine/stale-epoch
           (try (engine/advance (:model restarted) {:time-ms 152 :epoch 0} compiler)
                (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))))


(deftest seven-eighth-meter-one-shot-and-release-use-quarter-note-beat-boundaries
  (let [show (assoc-in (musical-show) [:transport :meter :beats-per-bar] 3.5)
        launched (control! show {:op :cue/launch :cue-id :music :launch {:mode :one-shot}})
        id (first (keys (:instances launched)))
        released (at-beat launched 1875 3.75)
        finished (at-beat (:model released) 2000 4.0)]
    (is (= 3.5 (get-in launched [:instances id :duration-timer :duration :value])))
    (is (= :releasing (get-in released [:model :instances id :phase])))
    (is (= 3.5 (get-in released [:model :instances id :release-at-beat])))
    (is (= 1750.0 (get-in released [:model :instances id :release-at-ms])))
    (is (empty? (get-in finished [:model :instances])))))

(deftest reused-steps-observe-current-inputs-and-rebind-on-hot-reload
  (let [calls (atom [])
        step (fn [version]
               (reuse/step {:pure? true :inputs [[:frame :variables :global] [:instance :params :level]]}
                          (fn [inputs]
                            (swap! calls conj version)
                            {:assignments [{:target-id :spot :attribute :dimmer
                                            :value (* (get-in inputs [:frame :variables :global])
                                                      (get-in inputs [:instance :params :level]))
                                            :version version}]})))
        steps {1 (step 1) 2 (step 2)}
        compile #(get steps (:version %))
        start (model (instance "a" :reload-policy :preserve-state))]
    (with-open [pool (executor/create {:workers 2 :queue-size 2 :timeout-ms 2000})]
      (let [advance #(engine/advance %1 {:time-ms %2} compile (executor/mapper pool))
            first-frame (advance start 1)
            second-frame (advance (:model first-frame) 2)
            changed (advance (assoc-in (:model second-frame) [:variables :global] 0.5) 3)
            reloaded (advance (assoc-in (:model changed) [:registry :effects :pulse :version] 2) 4)]
        (is (= [1 1 2] @calls))
        (is (= [0.75 0.75 0.375 0.375]
               (mapv #(get-in % [:assignments 0 :value]) [first-frame second-frame changed reloaded])))
        (is (= 2 (get-in reloaded [:assignments 0 :version])))
        (is (= [:effect/reloaded] (mapv :type (:intents reloaded))))))))

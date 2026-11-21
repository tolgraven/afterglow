(ns afterglow.control.model-test
  (:require [clojure.test :refer [deftest is testing]]
            [afterglow.control.model :as model]
            [afterglow.control.params :as params]
            [afterglow.control.views :as views]))

(def effect
  {:id :wash :version 1 :duration-ms 500 :envelope {:release-ms 100}
   :params {:level {:type :number :default 0.5 :bounds [0 1]}
            :color {:type :color :default [1 0 0]}
            :enabled {:type :boolean :default true}
            :count {:type :integer :default 2 :bounds [1 8]}
            :shape {:type :enum :default :sine :values [:sine :triangle]}}
   :outputs {:dimmer {:op :param :key :level}}})

(defn command [show operation]
  (merge {:show-id (:show-id show) :epoch (:epoch show) :source :test
          :command-id (str "cmd-" (:epoch show) "-" (:revision show))
          :time-ms (:time-ms show)} operation))

(defn apply! [show operation]
  (let [result (model/apply-command show (command show operation))]
    (when-not (= :accepted (get-in result [:ack :status]))
      (throw (ex-info "Test command rejected" (:ack result))))
    (:model result)))

(defn configured
  ([] (configured {}))
  ([options]
   (-> (model/new-show options)
       (apply! {:op :registry/publish :kind :effects :definition effect})
       (apply! {:op :cue/put :cue {:id :red :effect-id :wash :params {:level 0.6}}}))))

(deftest construction-is-inert-and-validates-basic-shape
    (is (= {:bpm 120 :playing? true :beat 0.0 :meter {:beats-per-bar 4 :bars-per-phrase 4}}
           (:transport (model/new-show))))
  (is (= {} (:instances (model/new-show))))
  (doseq [options [{:history-limit 0} {:epoch -1} {:revision 0.5} {:time-ms Double/NaN}
                   {:master 2} {:blackout? :yes} {:instances []} {:show-id nil}]]
    (is (thrown? clojure.lang.ExceptionInfo (model/new-show options)))))

(deftest publication-captures-versions-and-validates-cues
  (let [first-show (configured)
        second-show (apply! first-show {:op :registry/publish :kind :effects
                                       :definition (assoc effect :version 2)})]
    (is (= effect (get-in second-show [:registry :versions [:effects :wash 1]])))
    (is (= 2 (get-in second-show [:registry :effects :wash :version])))
    (is (= 3 (get-in second-show [:registry :revision])))
    (is (= 3 (get-in (apply! second-show {:op :registry/publish :kind :effects
                                         :definition (assoc effect :version 2)})
                     [:registry :revision])))
    (is (= 1 (get-in second-show [:registry :cues :red :version])))
    (is (= :unknown-effect
           (get-in (model/apply-command second-show
                       (command second-show {:op :cue/put :cue {:id :bad :effect-id :missing}})) [:ack :code])))
    (is (= :stale-definition-version
           (get-in (model/apply-command second-show
                       (command second-show {:op :registry/publish :kind :effects :definition effect})) [:ack :code])))
    (is (= 2 (get-in (apply! first-show {:op :cue/put :cue {:id :red :effect-id :wash}})
                     [:registry :cues :red :version])))))

(deftest malformed-input-is-a-rejection-not-an-exception-or-partial-update
  (let [show (configured)]
    (doseq [operation [{:op :cue/launch :cue-id :red :launch {:params 3}}
                       {:op :cue/launch :cue-id :red :launch []}
                       {:op :cue/put :cue 5}
                       {:op :registry/publish :kind :bogus :definition effect}
                       {:op :registry/publish :kind :effects :definition (assoc effect :version 2 :params {:x {:type :enum :default 1 :values 7}})}
                       {:op :master/set :value Double/NaN}
                       {:op :master/set :value 2}
                       {:op :blackout/set :value 1}
                       {:op :transport/set :transport {:other :value}}
                       {:op :transport/set :transport {:bpm 0}}]]
      (let [result (model/apply-command show (command show operation))]
        (is (= :rejected (get-in result [:ack :status])) (str operation))
        (is (identical? show (:model result)))
        (is (empty? (:events result))))))
  (is (= :invalid-command (get-in (model/apply-command (model/new-show) nil) [:ack :code]))))

(deftest launch-uses-defaults-overrides-and-captured-version
  (let [show (configured)
        result (model/apply-command show
                 (command show {:op :cue/launch :cue-id :red :time-ms 10
                                :gesture-id "press-1"
                                :launch {:mode :one-shot :params {:level 0.8}}}))
        id (get-in result [:ack :instance-id])
        instance (get-in result [:model :instances id])]
    (is (string? id))
    (is (= {:level 0.8 :color [1 0 0] :enabled true :count 2 :shape :sine} (:params instance)))
    (is (= effect (:definition instance)))
    (is (= 1 (:effect-version instance)))
    (is (= 500 (:duration-ms instance)))
    (is (= 100 (:release-duration-ms instance)))
    (is (= 10 (:started-at-ms instance)))
    (is (= :pinned (:reload-policy instance)))
    (is (= "press-1" (:gesture-id instance)))
    (is (= :test (:source instance)))
    (is (= :running (:phase instance)))
    (is (= 3 (get-in result [:ack :revision])))
    (is (= result (model/apply-command show (command show {:op :cue/launch :cue-id :red :time-ms 10
                                                         :gesture-id "press-1" :launch {:mode :one-shot :params {:level 0.8}}}))))))

(deftest persistent-and-held-cues-do-not-inherit-expiry
  (doseq [mode [:persistent :held]]
    (let [show (apply! (configured) {:op :cue/launch :cue-id :red :launch {:mode mode}})
          instance (first (vals (:instances show)))]
      (is (not (contains? instance :duration-ms)))
      (is (= mode (:launch-mode instance))))))

(deftest timed-launch-and-reload-options-are-validated
  (let [show (-> (model/new-show)
                 (apply! {:op :registry/publish :kind :effects :definition (dissoc effect :duration-ms)})
                 (apply! {:op :cue/put :cue {:id :red :effect-id :wash}}))]
    (doseq [launch [{:mode :one-shot} {:mode :timed :duration-ms -1}
                   {:mode :wat} {:reload-policy :wat} {:release-duration-ms -1}]]
      (is (= :rejected (get-in (model/apply-command show (command show {:op :cue/launch :cue-id :red :launch launch})) [:ack :status]))))
    (is (= 200 (:duration-ms (first (vals (:instances (apply! show {:op :cue/launch :cue-id :red :launch {:mode :timed :duration-ms 200}})))))))))

(deftest parameter-writes-use-captured-schema-and-reject-invalid-values
  (let [show (apply! (configured) {:op :cue/launch :cue-id :red})
        id (first (keys (:instances show)))
        updated (apply! show {:op :param/set :instance-id id :param :level :value 0.9})]
    (is (= 0.9 (get-in updated [:instances id :params :level])))
    (doseq [[param value] [[:level 2] [:count 1.5] [:shape :square] [:enabled :yes]
                          [:color [1 0 0 1]] [:missing 0] [:level Double/NaN]]]
      (let [result (model/apply-command show (command show {:op :param/set :instance-id id :param param :value value}))]
        (is (= :invalid-params (get-in result [:ack :code])))
        (is (= show (:model result)))))))

(deftest releases-address-instance-and-do-not-reset-release-clock
  (let [show (-> (configured) (apply! {:op :cue/launch :cue-id :red})
                 (apply! {:op :cue/launch :cue-id :red}))
        [a b] (sort (keys (:instances show)))
        released (apply! show {:op :instance/end :instance-id a :time-ms 50})
        repeated (apply! released {:op :instance/end :instance-id a :time-ms 60})
        forced (apply! repeated {:op :instance/end :instance-id a :time-ms 70 :force? true})]
    (is (= :releasing (get-in released [:instances a :phase])))
    (is (= 50 (get-in repeated [:instances a :release-at-ms])))
    (is (= :running (get-in repeated [:instances b :phase])))
    (is (= #{b} (set (keys (:instances forced)))))
    (is (= :unknown-instance (get-in (model/apply-command forced (command forced {:op :instance/end :instance-id a})) [:ack :code])))))

(deftest retries-conflicts-and-bounded-history
  (let [show (configured {:history-limit 2})
        launch (command show {:op :cue/launch :cue-id :red})
        first-result (model/apply-command show launch)
        retry (model/apply-command (:model first-result) launch)
        conflict (model/apply-command (:model first-result) (assoc launch :cue-id :other))
        more (-> (:model first-result)
                 (apply! {:op :master/set :value 0.8})
                 (apply! {:op :master/set :value 0.7}))]
    (is (= (:ack first-result) (:ack retry)))
    (is (identical? (:model first-result) (:model retry)))
    (is (= [] (:events retry)))
    (is (= :command-id-conflict (get-in conflict [:ack :code])))
    (is (= 2 (count (get-in more [:control :history]))))
    (is (nil? (get-in more [:control :history (:command-id launch)])))))

(deftest revision-epoch-source-and-time-guards
  (let [show (configured)]
    (doseq [[change code] [[{:show-id :other} :wrong-show]
                           [{:epoch 9} :stale-epoch]
                           [{:expected-revision 0} :stale-revision]
                           [{:source nil} :invalid-command]
                           [{:time-ms -1} :invalid-time]]]
      (let [result (model/apply-command show (merge (command show {:op :master/set :value 0.5}) change))]
        (is (= code (get-in result [:ack :code])))
        (is (identical? show (:model result)))))
    (is (= :invalid-time (get-in (model/apply-command show (dissoc (command show {:op :cue/launch :cue-id :red}) :time-ms)) [:ack :code])))))

(deftest restart-invalidates-old-work-but-retains-authored-content
  (let [show (apply! (configured) {:op :cue/launch :cue-id :red})
        old-command (command show {:op :master/set :value 0.5})
        restarted (apply! show {:op :show/restart :time-ms 100})
        next-show (apply! restarted {:op :cue/launch :cue-id :red})]
    (is (= 1 (:epoch restarted)))
    (is (= {} (:instances restarted)))
    (is (= (:registry show) (:registry restarted)))
    (is (= :stale-epoch (get-in (model/apply-command restarted old-command) [:ack :code])))
    (is (= #{"1:1"} (set (keys (:instances next-show)))))))

(deftest pages-and-deletion-preserve-running-captured-definitions
  (let [show (-> (configured)
                 (apply! {:op :page/put :page {:id :main :cells {[0 0] :red [1 1] :red}}})
                 (apply! {:op :cue/launch :cue-id :red}))
        deleted (apply! show {:op :cue/delete :cue-id :red})]
    (is (= {} (get-in deleted [:pages :main :cells])))
    (is (= (:instances show) (:instances deleted)))
    (is (nil? (get-in deleted [:registry :cues :red])))
    (is (= :unknown-cue (get-in (model/apply-command deleted (command deleted {:op :cue/launch :cue-id :red})) [:ack :code])))
    (let [restored (apply! deleted {:op :cue/put :cue {:id :red :effect-id :wash :params {:level 0.2}}})]
      (is (= 2 (get-in restored [:registry :cues :red :version])))
      (is (= 0.6 (get-in restored [:registry :versions [:cues :red 1] :params :level]))))))

(deftest restored-instances-do-not-collide-with-new-ids-or-launch-order
  (let [show (apply! (configured) {:op :cue/launch :cue-id :red})
        restored (model/new-show (select-keys show [:registry :instances]))
        next-show (apply! restored {:op :cue/launch :cue-id :red})]
    (is (= 2 (count (:instances next-show))))
    (is (= [0 1] (sort (map :order (vals (:instances next-show))))))))

(deftest vector-range-and-enum-parameter-contract
  (is (params/valid-schema? {:type :vector :size 3 :default [0 0 0] :bounds [-1 1]}))
  (is (false? (params/valid-schema? {:type :vector :default [0 0]})))
  (is (params/valid-value? {:type :range :bounds [0 10]} [2 7]))
  (is (not (params/valid-value? {:type :range :bounds [0 10]} [7 2])))
  (is (not (params/valid-value? {:type :enum :values 8} :a))))

(deftest invalid-default-in-trusted-initial-registry-still-rejects-launch
  (let [show (-> (configured)
                 (assoc-in [:registry :effects :wash :params :level :default] 2)
                 (assoc-in [:registry :cues :red :params] {}))
        result (model/apply-command show (command show {:op :cue/launch :cue-id :red}))]
    (is (= :invalid-params (get-in result [:ack :code])))
    (is (identical? show (:model result)))
    (is (= [] (:events result)))))

(deftest cue-saved-parameters-are-versioned-portable-launch-defaults
  (let [started (apply! (configured) {:op :cue/launch :cue-id :red})
        id (first (keys (:instances started)))
        changed (-> started (apply! {:op :param/set :instance-id id :param :level :value 0.9})
                    (apply! {:op :param/set :instance-id id :param :color :value [0 1 0]}))
        command (command changed {:op :cue/save-params :cue-id :red :instance-id id :expected-version 1})
        result (model/apply-command changed command)
        saved (:model result)
        restarted (apply! saved {:op :show/restart})
        relaunched (apply! restarted {:op :cue/launch :cue-id :red})
        overridden (apply! restarted {:op :cue/launch :cue-id :red :launch {:params {:level 0.1}}})
        cleared (apply! saved {:op :cue/clear-saved-params :cue-id :red :expected-version 2})
        fresh (-> cleared (apply! {:op :show/restart}) (apply! {:op :cue/launch :cue-id :red}))]
    (is (= :accepted (get-in result [:ack :status])))
    (is (= 2 (get-in saved [:registry :cues :red :version])))
    (is (= 0.6 (get-in saved [:registry :cues :red :params :level])) "authored defaults remain separate")
    (is (= 0.9 (get-in saved [:registry :cues :red :saved-params :level])))
    (is (= (:instances changed) (:instances saved)))
    (is (= [:registry/published :cue/params-saved] (mapv :type (:events result))))
    (is (= (:ack result) (:ack (model/apply-command saved command))))
    (is (= 2 (get-in (:model (model/apply-command saved command)) [:registry :cues :red :version])))
    (is (= {:saved? true :color [0 1 0]}
           (select-keys (views/cue-view restarted :red) [:saved? :color])))
    (is (= 0.9 (:level (:params (first (vals (:instances relaunched)))))))
    (is (= 0.1 (:level (:params (first (vals (:instances overridden)))))))
    (is (= 3 (get-in cleared [:registry :cues :red :version])))
    (is (nil? (get-in cleared [:registry :cues :red :saved-params])))
    (is (= 0.9 (get-in cleared [:registry :versions [:cues :red 2] :saved-params :level])))
    (is (= (:instances saved) (:instances cleared)))
    (is (= 0.6 (:level (:params (first (vals (:instances fresh)))))))))

(deftest cue-preset-rejections-preserve-state-and-captured-schema-boundaries
  (let [show (-> (configured)
                 (apply! {:op :cue/put :cue {:id :other :effect-id :wash}})
                 (apply! {:op :cue/launch :cue-id :red}))
        id (first (keys (:instances show)))]
    (doseq [[operation code] [[{:op :cue/save-params :cue-id :other :instance-id id} :wrong-cue-instance]
                              [{:op :cue/save-params :cue-id :red :instance-id "missing"} :unknown-instance]
                              [{:op :cue/save-params :cue-id :missing :instance-id id} :unknown-cue]
                              [{:op :cue/save-params :cue-id :red :instance-id id :expected-version 9} :stale-definition-version]
                              [{:op :cue/clear-saved-params :cue-id :red :expected-version 9} :stale-definition-version]
                              [{:op :cue/put :cue {:id :bad :effect-id :wash :saved-params {:level 4}}} :invalid-params]]]
      (let [result (model/apply-command show (command show operation))]
        (is (= code (get-in result [:ack :code])))
        (is (identical? show (:model result)))
        (is (= [] (:events result)))))
    (let [changed (apply! show {:op :registry/publish :kind :effects
                               :definition (-> effect (assoc :version 2) (update :params dissoc :level))})
          result (model/apply-command changed (command changed {:op :cue/save-params :cue-id :red :instance-id id}))]
      (is (= :invalid-params (get-in result [:ack :code]))))
    (let [invalid (assoc-in show [:registry :cues :red :saved-params :level] 99)
          result (model/apply-command invalid (command invalid {:op :cue/launch :cue-id :red}))]
      (is (= :invalid-params (get-in result [:ack :code])))
      (is (identical? invalid (:model result))))))

(ns afterglow.control.model-test
  (:require [clojure.test :refer [deftest is testing]]
            [afterglow.control.model :as model]
            [afterglow.control.pages :as pages]
            [afterglow.control.params :as params]
            [afterglow.control.views :as views]
            [afterglow.runtime.events :as events]))

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

(deftest reorder-uses-captured-launch-ids-and-preserves-chronology
  (let [launch {:op :cue/launch :cue-id :red}
        show (-> (configured)
                 (apply! launch)
                 (apply! (assoc launch :launch {:params {:level 0.7}}))
                 (apply! launch)
                 (apply! (assoc launch :launch {:priority 10})))
        move {:op :instance/move-after :instance-id "0:1" :after-instance-id "0:3"
              :expected-revision (:revision show)}
        cmd (command show move)
        result (model/apply-command show cmd)
        moved (:model result)
        ids ["0:2" "0:3" "0:1" "0:4"]]
    (is (= :accepted (get-in result [:ack :status])))
    (is (= ids (get-in result [:ack :instance-ids])))
    (is (= [{:type :instances/reordered :instance-ids ids}] (:events result)))
    (is (= ids (mapv :id (:instances (views/snapshot moved)))))
    (is (= ["0:1" "0:2" "0:3" "0:4"] (:instances (views/cue-view moved :red))))
    (is (= (:instances show) (update-vals (:instances moved) #(dissoc % :render-order))))
    (is (identical? (get-in show [:instances "0:4"]) (get-in moved [:instances "0:4"])))
    (is (= {:model moved :ack (:ack result) :events []} (model/apply-command moved cmd)))
    (is (= ["0:2" "0:3" "0:1" "0:5" "0:4"]
           (mapv :id (:instances (views/snapshot (apply! moved launch))))))
    (is (= ids (mapv :id (:instances (views/snapshot (model/new-show moved))))))
    (let [after-release (apply! moved {:op :instance/end :instance-id "0:3"})
          relaunched (-> after-release (apply! {:op :instance/remove :instance-id "0:3"}) (apply! launch))]
      (doseq [[m op expected] [[moved move :stale-revision]
                               [after-release (dissoc move :expected-revision) :instance-not-running]
                               [relaunched (dissoc move :expected-revision) :unknown-instance]]]
        (let [rejected (model/apply-command m (command m op))]
          (is (= expected (get-in rejected [:ack :code])))
          (is (identical? m (:model rejected)))
          (is (empty? (:events rejected))))))))

(deftest standalone-cross-tier-reorder-preserves-authored-priority-and-accepts-an-existing-position
  (let [launch (fn [show priority]
                 (apply! show {:op :cue/launch :cue-id :red :launch {:priority priority}}))
        show (reduce launch (configured) [0 0 10 10 20])
        move (fn [model source target]
               (model/apply-command model (command model {:op :instance/move-after
                                                          :instance-id source :after-instance-id target})))
        adjacent (move show "0:3" "0:2")
        up (move show "0:1" "0:3")
        moved (:model up)
        down (move moved "0:1" "0:2")]
    (is (= :accepted (get-in adjacent [:ack :status])))
    (is (empty? (:events adjacent)))
    (is (identical? (:instances show) (get-in adjacent [:model :instances])))
    (is (= ["0:2" "0:3" "0:1" "0:4" "0:5"] (get-in up [:ack :instance-ids])))
    (is (= (assoc (get-in show [:instances "0:1"]) :render-priority 10 :render-order 1)
           (get-in moved [:instances "0:1"])))
    (is (identical? (get-in show [:instances "0:5"]) (get-in moved [:instances "0:5"])))
    (is (= ["0:2" "0:3" "0:1" "0:4" "0:6" "0:5"]
           (mapv :id (:instances (views/snapshot (launch moved 10))))))
    (is (= ["0:2" "0:1" "0:3" "0:4" "0:5"] (get-in down [:ack :instance-ids])))
    (is (nil? (get-in down [:model :instances "0:1" :render-priority])))))

(deftest seeded-shuffle-preserves-priorities-and-pins-releasing-and-layer-slots
  (let [launch {:op :cue/launch :cue-id :red}
        show (-> (reduce (fn [m priority] (apply! m (assoc launch :launch {:priority priority})))
                         (configured) [0 0.0 0 0 0 0 0 3 3 3])
                 (apply! {:op :instance/end :instance-id "0:3"})
                 (assoc-in [:instances "0:5" :source] {:adapter :test :native-layer {:id :macro :member 0}}))
        shuffled (fn [seed] (model/apply-command show (command show {:op :instances/shuffle :seed seed})))
        result (shuffled 31)
        ids (get-in result [:ack :instance-ids])]
    (is (= :accepted (get-in result [:ack :status])))
    (is (= result (shuffled 31)))
    (is (not= ids (get-in (shuffled 37) [:ack :instance-ids])))
    (is (= ["0:3" "0:5"] (mapv ids [2 4])))
    (is (= #{"0:8" "0:9" "0:10"} (set (subvec ids 7))))
    (is (= (:instances show) (update-vals (get-in result [:model :instances]) #(dissoc % :render-order))))
    (is (= :invalid-seed (get-in (shuffled 9223372036854775808N) [:ack :code])))))

(deftest reorder-rejects-ambiguous-compound-positions-atomically
  (let [launch {:op :cue/launch :cue-id :red}
        show (-> (configured)
                 (apply! (assoc launch :source {:adapter :test :native-layer {:id :a :member 0}}))
                 (apply! launch)
                 (apply! (assoc launch :source {:adapter :test :native-layer {:id :a :member 1}}))
                 (apply! launch))
        mixed (assoc-in show [:instances "0:3" :priority] 1)]
    (doseq [[m source target code] [[show "0:1" "0:3" :same-render-unit]
                                    [show "0:4" "0:1" :interleaved-native-layer]
                                    [mixed "0:4" "0:1" :priority-mismatch]]]
      (let [result (model/apply-command m (command m {:op :instance/move-after
                                                       :instance-id source :after-instance-id target}))]
        (is (= code (get-in result [:ack :code])))
        (is (identical? m (:model result)))
        (is (empty? (:events result)))))))

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

(deftest effect-edits-preserve-dependent-cue-presets
  (let [pin {:id :pinned :effect-id :wash :effect-version 1 :saved-params {:level 0.9}}
        show (-> (configured)
                 (apply! {:op :cue/put :cue pin})
                 (apply! {:op :cue/put :cue {:id :saved :effect-id :wash :saved-params {:level 0.8}}})
                 (apply! {:op :cue/launch :cue-id :red}))
        edit {:op :registry/publish :kind :effects
              :definition (-> effect (assoc :version 2) (assoc-in [:params :level :bounds] [0 0.5]))}
        rejected (model/apply-command show (command show edit))
        repaired (-> show
                     (apply! {:op :cue/put :cue {:id :red :effect-id :wash :params {:level 0.4}}})
                     (apply! {:op :cue/delete :cue-id :saved})
                     (apply! edit))
        launch (model/apply-command repaired (command repaired {:op :cue/launch :cue-id :pinned}))]
    (is (= :incompatible-cue-presets (get-in rejected [:ack :code])))
    (is (= #{[:cues :red :params :level] [:cues :saved :saved-params :level]}
           (set (map :path (get-in rejected [:ack :details :errors])))))
    (is (identical? show (:model rejected)))
    (is (empty? (:events rejected)))
    (is (= 2 (get-in repaired [:registry :effects :wash :version])))
    (is (= 0.9 (get-in launch [:model :instances (get-in launch [:ack :instance-id]) :params :level])))))

(deftest narrowing-color-component-bounds-checks-the-cue-preset
  (let [show (apply! (configured) {:op :cue/put :cue {:id :accent :effect-id :wash
                                                       :effect-version false
                                                       :saved-params {:color [0.7 0.2 0.1]}}})
        revised (-> effect (assoc :version 2)
                    (assoc-in [:params :color] {:type :color :bounds [0 0.5] :default [0.5 0 0]}))
        result (model/apply-command show (command show {:op :registry/publish :kind :effects
                                                        :definition revised}))]
    (is (= [[:cues :accent :saved-params :color]] (mapv :path (get-in result [:ack :details :errors]))))
    (is (identical? show (:model result)))))

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

(def ^:private studio-operator {:operator-id "studio-panel"})

(defn- operator-command [show {:keys [op] :as operation}]
  (command show (if (#{:history/undo :history/redo :history/select} op)
                  (merge {:expected-history-position (get-in show [:control :edit-history :position] 0)} operation)
                  operation)))

(defn- operator! [show operation]
  (let [{:keys [model ack]} (model/apply-command show (operator-command show operation) studio-operator)]
    (when-not (= :accepted (:status ack))
      (throw (ex-info "Operator command rejected" ack)))
    model))

(defn- knob [id param gesture-id]
  {:instance-id id :param param :control-id :knob :gesture-id gesture-id})

(defn- turn! [show gesture value]
  (-> show
      (operator! (assoc gesture :op :gesture/begin))
      (operator! (assoc gesture :op :gesture/sample :sequence 1 :value value))
      (operator! (assoc gesture :op :gesture/end :last-sequence 1))))

(deftest operator-edits-use-separate-authority-and-existing-receipts
  (let [show (events/begin (apply! (configured) {:op :cue/launch :cue-id :red}))
        id (first (keys (:instances show)))
        gesture (assoc (knob id :level :gesture-a)
                       :source {:adapter :forged :operator-id "studio-panel"} :actor "forged")
        begin-command (command show (assoc gesture :op :gesture/begin))
        forged (model/apply-command show begin-command)
        started (operator! show (assoc gesture :op :gesture/begin))
        value-command (command started (assoc gesture :op :gesture/sample :sequence 1 :value 0.8))
        {:keys [model ack] :as sampled} (model/apply-command started value-command studio-operator)
        duplicate (model/apply-command model value-command studio-operator)
        replay-forged (model/apply-command model value-command)
        replay-other (model/apply-command model value-command {:operator-id "other-panel"})
        ended (operator! model (assoc gesture :op :gesture/end :last-sequence 1
                                     :target-display {:cue-id :forged :cue-label "Forged"}))
        undone (operator! ended {:op :history/undo :expected-cursor 1})
        ordinary (apply! show (assoc gesture :op :param/set :value 0.7))]
    (is (= :operator-required (get-in forged [:ack :code])))
    (is (identical? show (:model forged)))
    (is (= 0.8 (get-in model [:instances id :params :level])))
    (is (= 0 (get-in model [:control :edit-history :cursor])))
    (is (= [{:type :param/changed :instance-id id :param :level :value 0.8}] (:events sampled)))
    (is (= {:kind :command :id "studio-panel"} (:emitter (last (events/pending model)))))
    (is (= ack (:ack duplicate)))
    (is (identical? model (:model duplicate)))
    (is (empty? (:events duplicate)))
    (is (= :operator-required (get-in replay-forged [:ack :code])))
    (is (= :command-id-conflict (get-in replay-other [:ack :code])))
    (is (= "studio-panel" (get-in ended [:control :edit-history :nodes 1 :actor])))
    (is (= {:cue-id :red :cue-label "red" :effect-id :wash :effect-label "wash"}
           (get-in ended [:control :edit-history :nodes 1 :target-display])))
    (is (= 0.6 (get-in undone [:instances id :params :level])))
    (is (= 0.7 (get-in ordinary [:instances id :params :level])))
    (is (nil? (get-in ordinary [:control :edit-history])))))

(deftest unrelated-parameters-undo-after-an-external-aba-write
  (let [show (apply! (configured) {:op :cue/launch :cue-id :red})
        id (first (keys (:instances show)))
        target [:instance-param id :level]
        edits (-> show (turn! (knob id :level :gesture-a) 0.8)
                       (turn! (knob id :count :gesture-b) 4))
        repeated (apply! edits {:op :param/set :instance-id id :param :level :value 0.8})
        automated (-> repeated
                      (apply! {:op :param/set :instance-id id :param :level :value 0.7})
                      (apply! {:op :param/set :instance-id id :param :level :value 0.8}))
        separate-undo (operator! automated {:op :history/undo :expected-cursor 2})
        conflict (model/apply-command separate-undo
                   (operator-command separate-undo {:op :history/undo :expected-cursor 1}) studio-operator)]
    (is (= 0 (get-in repeated [:control :edit-history :generations target])))
    (is (= 2 (get-in automated [:control :edit-history :generations target])))
    (is (= 2 (get-in separate-undo [:instances id :params :count])))
    (is (= 0.8 (get-in separate-undo [:instances id :params :level])))
    (is (= :history-conflict (get-in conflict [:ack :code])))
    (is (= target (get-in conflict [:ack :details :target])))
    (is (identical? separate-undo (:model conflict)))
    (is (empty? (:events conflict)))))

(deftest canceled-edits-preserve-redo-and-validate-samples
  (let [show (apply! (configured) {:op :cue/launch :cue-id :red})
        id (first (keys (:instances show)))
        target [:instance-param id :count]
        undone (-> show (turn! (knob id :count :gesture-a) 4)
                   (operator! {:op :history/undo :expected-cursor 1}))
        gesture (knob id :count :gesture-b)
        open (operator! undone (assoc gesture :op :gesture/begin))
        sample (assoc gesture :op :gesture/sample :sequence 1 :value 3)
        invalid (model/apply-command open (command open (assoc sample :value 3.5)) studio-operator)
        other (model/apply-command open (command open sample) {:operator-id "other-panel"})
        sampled (operator! open sample)
        canceled (model/apply-command sampled (command sampled (assoc gesture :op :gesture/cancel))
                                      studio-operator)
        redone (operator! (:model canceled) {:op :history/redo :expected-cursor 0 :node-id 1})]
    (is (= :invalid-params (get-in invalid [:ack :code])))
    (is (identical? open (:model invalid)))
    (is (= :unknown-gesture (get-in other [:ack :code])))
    (is (identical? open (:model other)))
    (is (= 3 (get-in sampled [:instances id :params :count])))
    (is (= [{:type :param/changed :instance-id id :param :count :value 2}] (:events canceled)))
    (is (nil? (get-in canceled [:model :control :edit-history :open target])))
    (is (= 0 (get-in canceled [:ack :history-cursor])))
    (is (= 4 (get-in redone [:instances id :params :count])))
    (is (= 1 (get-in redone [:control :edit-history :cursor])))))

(deftest history-travel-validates-all-final-writes-before-commit
  (let [show (apply! (configured) {:op :cue/launch :cue-id :red})
        id (first (keys (:instances show)))
        edits (-> show (turn! (knob id :level :gesture-a) 0.8)
                       (turn! (knob id :count :gesture-b) 4))
        selection {:op :history/select :expected-cursor 2 :node-id 0}
        valid (model/apply-command edits (operator-command edits selection) studio-operator)
        reloaded (assoc-in edits [:instances id :definition :params :level :bounds] [0.7 1.0])
        invalid (model/apply-command reloaded (operator-command reloaded selection) studio-operator)]
    (is (= :accepted (get-in valid [:ack :status])))
    (is (= [:count :level] (mapv :param (:events valid))))
    (is (= 0 (get-in valid [:model :control :edit-history :cursor])))
    (is (= :invalid-params (get-in invalid [:ack :code])))
    (is (identical? reloaded (:model invalid)))
    (is (empty? (:events invalid)))
    (is (= 4 (get-in (:model invalid) [:instances id :params :count])))
    (is (= 2 (get-in (:model invalid) [:control :edit-history :cursor])))))

(deftest history-generations-follow-retention-and-clear-on-restart
  (let [show (apply! (configured) {:op :cue/launch :cue-id :red})
        id (first (keys (:instances show)))
        first-edit (turn! show (knob id :level :gesture-a) 0.8)
        pruned (turn! (assoc-in first-edit [:control :edit-history :limit] 2)
                      (knob id :count :gesture-b) 4)
        open (operator! pruned (assoc (knob id :level :gesture-c) :op :gesture/begin))
        late-sample (command open (assoc (knob id :level :gesture-c) :op :gesture/sample
                                        :sequence 1 :value 0.9))
        restart (apply! open {:op :show/restart})
        rejected (model/apply-command restart late-sample studio-operator)
        root-undo (model/apply-command restart (operator-command restart {:op :history/undo :expected-cursor 0})
                                       studio-operator)]
    (is (= {[:instance-param id :count] 0} (get-in pruned [:control :edit-history :generations])))
    (is (seq (get-in open [:control :edit-history :open])))
    (is (nil? (get-in restart [:control :edit-history])))
    (is (= :stale-epoch (get-in rejected [:ack :code])))
    (is (= :at-history-root (get-in root-undo [:ack :code])))
    (is (identical? restart (:model root-undo)))))

(deftest an-evicted-undo-cannot-replay-after-redo-returns-to-the-same-tip
  (let [show (apply! (configured) {:op :cue/launch :cue-id :red})
        id (first (keys (:instances show)))
        edited (turn! show (knob id :level :gesture-a) 0.8)
        undo (operator-command edited {:op :history/undo :expected-cursor 1})
        undone (model/apply-command edited undo studio-operator)
        redone (operator! (:model undone) {:op :history/redo :expected-cursor 0 :node-id 1})
        cached (model/apply-command redone undo studio-operator)
        evicted (reduce (fn [model _] (apply! model {:op :master/set :value 0.9})) redone (range 1024))
        replayed (model/apply-command evicted undo studio-operator)
        fresh (operator-command evicted {:op :history/undo :expected-cursor 1})
        incomplete (model/apply-command evicted (dissoc fresh :expected-history-position) studio-operator)
        disengaged (model/apply-command evicted fresh studio-operator)]
    (is (= 2 (get-in undone [:ack :history-position])))
    (is (= (:ack undone) (:ack cached)))
    (is (identical? redone (:model cached)))
    (is (nil? (get-in evicted [:control :history (:command-id undo)])))
    (is (= [1 3] ((juxt :cursor :position) (get-in evicted [:control :edit-history]))))
    (is (= 0.8 (get-in evicted [:instances id :params :level])))
    (doseq [result [replayed incomplete]]
      (is (= :stale-history-position (get-in result [:ack :code])))
      (is (identical? evicted (:model result)))
      (is (empty? (:events result))))
    (is (= [:accepted 0 4] ((juxt :status :history-cursor :history-position) (:ack disengaged))))
    (is (= 0.6 (get-in disengaged [:model :instances id :params :level])))))

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

(defn- recent-cue-ids [show]
  (mapv (comp :id :cue) (:cells (views/page-view show pages/recent-page-id))))

(deftest recent-page-holds-the-last-64-distinct-launches-in-grid-order
  (let [ids (mapv #(str "cue-" %) (range 66))
        launch (fn [show id] (apply! show {:op :cue/launch :cue-id id}))
        authored (configured {:history-limit 2})
        published (reduce (fn [show id] (apply! show {:op :cue/put :cue {:id id :effect-id :wash}}))
                          authored ids)
        show (reduce launch published ids)
        page (views/page-view show pages/recent-page-id)
        expected (vec (reverse (drop 2 ids)))
        revisited (launch show (peek expected))
        stale (update-in show [:registry :cues] dissoc (first expected))]
    (is (empty? (recent-cue-ids published)))
    (is (= {:id pages/recent-page-id :name "Recent cues" :columns 8 :rows 8}
           (dissoc page :cells)))
    (is (= (for [y (range 7 -1 -1) x (range 8)] [x y])
           (map (juxt :x :y) (:cells page))))
    (is (= expected (recent-cue-ids show)))
    (is (= expected
           (mapv (fn [{:keys [x y]}] (pages/cue-id-at show pages/recent-page-id [x y])) (:cells page))))
    (is (= (into [(peek expected)] (pop expected)) (recent-cue-ids revisited)))
    (is (= (recent-cue-ids revisited) (recent-cue-ids (launch revisited (peek expected)))))
    (is (= (into [(first ids)] (rest expected)) (recent-cue-ids (launch stale (first ids)))))
    (is (identical? (:pages authored) (:pages revisited)))
    (is (= page (peek (:pages (views/snapshot show)))))))

(deftest recent-page-records-only-new-successful-cue-launches
  (let [show (-> (configured)
                 (apply! {:op :cue/put :cue {:id :blue :effect-id :wash}}))
        red (command show {:op :cue/launch :cue-id :red})
        launched (:model (model/apply-command show red))
        latest (apply! launched {:op :cue/launch :cue-id :blue})]
    (doseq [[operation error] [[{:op :cue/launch :cue-id :missing} :unknown-cue]
                               [{:op :cue/launch :cue-id :red :launch {:params {:level 10}}} :invalid-params]]]
      (let [result (model/apply-command latest (command latest operation))]
        (is (= error (get-in result [:ack :code])))
        (is (identical? latest (:model result)))))
    (let [retry (model/apply-command latest red)]
      (is (identical? latest (:model retry)))
      (is (empty? (:events retry))))
    (is (= [:blue :red] (recent-cue-ids latest)
           (recent-cue-ids (apply! latest {:op :effect/launch :effect-id :wash}))
           (recent-cue-ids (apply! latest {:op :show/restart}))))))

(deftest recent-page-resolves-live-cue-edits-and-forgets-deleted-cues
  (let [launch {:op :cue/launch :cue-id :red}
        original (-> (configured)
                     (apply! {:op :cue/put :cue {:id :blue :effect-id :wash}})
                     (apply! {:op :cue/launch :cue-id :blue})
                     (apply! launch))
        replace {:op :cue/put :cue {:id :red :effect-id :wash :name "Updated red"}}
        updated (apply! original replace)
        stale (update-in updated [:registry :cues] dissoc :red)
        deleted (apply! updated {:op :cue/delete :cue-id :red})
        restored (apply! deleted replace)]
    (is (= "Updated red" (get-in (views/page-view updated pages/recent-page-id) [:cells 0 :cue :name])))
    (is (nil? (pages/cue-id-at stale pages/recent-page-id [0 7])))
    (is (= [:blue] (recent-cue-ids stale) (recent-cue-ids (apply! stale replace))
           (recent-cue-ids deleted) (recent-cue-ids restored)))
    (is (= :blue (pages/cue-id-at deleted pages/recent-page-id [0 7])))
    (is (= [:red :blue] (recent-cue-ids (apply! restored launch))))))

(deftest recent-page-id-cannot-conflict-with-an-authored-page
  (let [string-id (first pages/recent-page-id)
        keyword-id (keyword string-id)
        original (configured)
        show (reduce (fn [show id] (apply! show {:op :page/put :page {:id id :cells {[0 0] :red}}}))
                     original [string-id keyword-id])]
    (doseq [[page-id embedded-id] [[pages/recent-page-id :main] [:main pages/recent-page-id]]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"generated recent page ID"
                            (model/new-show {:pages {page-id {:id embedded-id}}}))))
    (let [authored (sorted-map :main {:id :main :cells {}})
          sorted-show (model/new-show {:pages authored})
          result (model/apply-command sorted-show
                                     (command sorted-show {:op :page/delete :page-id pages/recent-page-id}))]
      (is (= authored (:pages sorted-show)))
      (is (= :unknown-page (get-in result [:ack :code])))
      (is (identical? sorted-show (:model result))))
    (is (= [keyword-id string-id pages/recent-page-id] (pages/page-ids show)))
    (doseq [[operation expected-error]
            [[{:op :page/put :page {:id pages/recent-page-id}} :invalid-page]
             [{:op :page/delete :page-id pages/recent-page-id} :unknown-page]]]
      (let [result (model/apply-command show (command show operation))]
        (is (= expected-error (get-in result [:ack :code])))
        (is (identical? show (:model result)))))
    (doseq [id [string-id keyword-id]]
      (is (= :red (pages/cue-id-at show id [0 0]))))))

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
    (let [without-override (apply! show {:op :cue/put :cue {:id :red :effect-id :wash}})
          changed (apply! without-override {:op :registry/publish :kind :effects
                               :definition (-> effect (assoc :version 2) (update :params dissoc :level))})
          result (model/apply-command changed (command changed {:op :cue/save-params :cue-id :red :instance-id id}))]
      (is (= :invalid-params (get-in result [:ack :code]))))
    (let [invalid (assoc-in show [:registry :cues :red :saved-params :level] 99)
          result (model/apply-command invalid (command invalid {:op :cue/launch :cue-id :red}))]
      (is (= :invalid-params (get-in result [:ack :code])))
      (is (identical? invalid (:model result))))))

(deftest launch-registered-effect-without-any-cue-or-grid-cell
  (let [show (assoc-in (configured) [:registry :cues] {})
        result (model/apply-command show (command show {:op :effect/launch :effect-id :wash
                                                       :launch {:mode :one-shot :duration {:beats 1/2}}}))
        id (get-in result [:ack :instance-id])
        instance (get-in result [:model :instances id])]
    (is (= :accepted (get-in result [:ack :status])))
    (is (nil? (:cue-id instance)))
    (is (= :wash (:effect-id instance)))
    (is (= {:beats 1/2} (:duration instance)))
    (is (= (:registry show) (get-in result [:model :registry])))
    (is (= :unknown-effect (get-in (model/apply-command show (command show {:op :effect/launch :effect-id :absent})) [:ack :code])))))

(deftest only-accepted-reducer-events-join-the-frame-batch
  (let [base (configured)
        cmd (command base {:op :cue/launch :cue-id :red})
        first-result (model/apply-command (events/begin base) cmd)
        repeated (model/apply-command (:model first-result) cmd)
        bad (model/apply-command (:model repeated) (command base {:op :cue/launch :cue-id :missing}))]
    (is (= (map :event (events/pending (:model bad))) (:events first-result)))
    (is (seq (:events first-result)))
    (is (= (events/finish (:model bad)) (:model (model/apply-command base cmd))))
    (is (empty? (events/pending base)))))

(deftest launch-restricts-an-instance-without-changing-its-published-effect
  (let [m (configured)
        result (apply! m {:op :cue/launch :cue-id :red :launch {:targets [:left "right"]}})
        i (first (vals (:instances result)))]
    (is (= [:left "right"] (:targets i)))
    (is (= effect (:definition i) (get-in result [:registry :effects :wash])))
    (doseq [targets [nil 1 [:left :left] [:left nil]]]
      (is (= :invalid-targets (get-in (model/apply-command m (command m {:op :effect/launch :effect-id :wash
                                                                        :launch {:targets targets}})) [:ack :code]))))))

(deftest domain-command-uses-the-shared-receipts-and-event-batch
  (let [base (events/begin (model/new-show))
        cmd (command base {:op :example/set :value 1 :expected-revision 0})
        changed {:type :example/changed :value 1}
        operation (fn [m {:keys [value]}]
                    (when (neg? value)
                      (throw (ex-info "Invalid value" {:control/error :invalid-value})))
                    {:model (assoc-in m [:settings :example] value)
                     :events [changed] :result {:value value}})
        result (model/apply-domain-command base cmd operation)
        updated (:model result)
        duplicate (model/apply-domain-command updated cmd operation)]
    (is (= {:status :accepted :revision 1 :value 1}
           (select-keys (:ack result) [:status :revision :value])))
    (is (= 1 (get-in updated [:settings :example])))
    (is (= [changed] (mapv :event (events/pending updated))))
    (is (= (:ack result) (:ack duplicate)))
    (is (identical? updated (:model duplicate)))
    (is (= [] (:events duplicate)))
    (doseq [[code m c] [[:wrong-show base (assoc cmd :show-id :other)]
                        [:stale-epoch base (assoc cmd :epoch 1)]
                        [:stale-revision updated (assoc cmd :command-id :new)]
                        [:command-id-conflict updated (assoc cmd :value 2)]
                        [:invalid-value base (assoc cmd :value -1)]]]
      (let [rejected (model/apply-domain-command m c operation)]
        (is (= code (get-in rejected [:ack :code])))
        (is (identical? m (:model rejected)))))))

(deftest host-domain-admission-preserves-an-open-operator-gesture
  (let [show (apply! (configured) {:op :cue/launch :cue-id :red})
        id (first (keys (:instances show)))
        gesture (knob id :level :interleaved)
        started (operator! show (assoc gesture :op :gesture/begin))
        cmd (command started {:op :example/set :value 0.5})
        operation (fn [m {:keys [value]}] {:model (assoc-in m [:settings :example] value)})
        mixed (model/apply-domain-command started cmd operation)
        mixed-model (:model mixed)
        sample (operator-command mixed-model
                                 (assoc gesture :op :gesture/sample :sequence 1 :value 0.8
                                        :source {:adapter :guest :operator-id "studio-panel"}))
        forged (model/apply-domain-command
                 mixed-model sample
                 (fn [& _] (throw (AssertionError. "Reserved history operations must use owner admission"))))
        sampled (model/apply-command mixed-model sample studio-operator)
        ended (operator! (:model sampled) (assoc gesture :op :gesture/end :last-sequence 1))
        undo (operator! ended {:op :history/undo :expected-cursor 1})]
    (is (= :accepted (get-in mixed [:ack :status])))
    (is (= 0.5 (get-in mixed-model [:settings :example])))
    (is (= (get-in started [:control :edit-history])
           (get-in mixed-model [:control :edit-history])))
    (is (= :operator-required (get-in forged [:ack :code])))
    (is (identical? mixed-model (:model forged)))
    (is (= :accepted (get-in sampled [:ack :status])))
    (is (= 0.8 (get-in ended [:instances id :params :level])))
    (is (= 0.6 (get-in undo [:instances id :params :level])))
    (is (= 0.5 (get-in undo [:settings :example])))
    (is (= (:ack mixed) (:ack (model/apply-domain-command undo cmd operation))))))

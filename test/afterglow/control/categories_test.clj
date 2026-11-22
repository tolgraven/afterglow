(ns afterglow.control.categories-test
  (:require [clojure.test :refer [deftest is]]
            [afterglow.control.categories :as categories]
            [afterglow.control.model :as model]
            [afterglow.control.views :as views]))

(defn command [show payload]
  (merge {:op :cue/launch :source :test :show-id (:show-id show) :epoch (:epoch show)
          :command-id (str (:epoch show) "/" (:revision show)) :time-ms (:time-ms show)} payload))
(defn apply! [show payload]
  (let [result (model/apply-command show (command show payload))]
    (when-not (= :accepted (get-in result [:ack :status])) (throw (ex-info "Rejected test command" (:ack result))))
    (:model result)))
(defn show []
  (reduce (fn [show definition]
            (-> show
                (apply! {:op :registry/publish :kind :effects :definition definition})
                (apply! {:op :cue/put :cue {:id (:id definition) :effect-id (:id definition) :color [1 0 0]}})
                (apply! {:op :cue/launch :cue-id (:id definition)})))
          (model/new-show)
          [{:id :wash :version 1 :params {} :outputs {:color [1 0 0] :dimmer 1} :categories [:front]}
           {:id :move :version 1 :params {} :outputs [{:attribute :aim :value [0 0 1]}]}
           {:id :flash :version 1 :params {} :outputs {:strobe 1 :dimmer 1}}]))

(deftest derived-categories-are-output-union-plus-tags-and-not-cue-swatch
  (is (= [:color :front :intensity]
         (categories/definition-categories {:outputs {:color 1 :dimmer 1} :categories [:front :color]})))
  (is (= [:beam-shape :movement]
         (categories/definition-categories {:outputs [{:attribute :aim} {:attribute :focus}]})))
  (is (= [:modulation] (categories/definition-categories {:modulation {}})))
  (is (= [] (categories/definition-categories {:color [1 0 0]})))
  (let [view (views/snapshot (show))]
    (is (= [:color :front :intensity] (:categories (views/cue-view (show) :wash))))
    (is (= [1 0 0] (:color (views/cue-view (show) :wash))))
    (is (= "#70bedb" (:color (first (filter #(= :movement (:id %)) (:groups view))))))
    (is (every? #(= #{:opacity :paused?} (set (keys (:system %)))) (:instances view)))))

(deftest selector-dimensions-intersect-and-categories-support-any-or-all
  (let [show (show), ids #(mapv :cue-id (categories/select-instances show %))]
    (is (= [:wash :move :flash] (ids {})))
    (is (= [:wash :flash] (ids {:categories [:color :intensity]})))
    (is (= [:wash] (ids {:categories [:color :intensity] :match :all})))
    (is (= [:flash] (ids {:categories [:intensity] :cue-ids [:flash]})))
    (is (= [] (ids {:categories [] :match :all})))
    (is (= [] (ids {:effect-ids []})))
    (doseq [selector [nil {:other []} {:match :bogus} {:categories ["movement"]}
                      {:instance-ids ["missing"]} {:cue-ids [:wash :wash]}]]
      (is (thrown? clojure.lang.ExceptionInfo (ids selector))))))

(deftest bulk-controls-are-atomic-retry-safe-and-do-not-alter-authored-params
  (let [show (show), cmd (command show {:op :group/apply :selector {:categories [:intensity]}
                                      :action {:op :instance/opacity-set :value 0.25}})
        result (model/apply-command show cmd), changed (:model result)
        ids (get-in result [:ack :instance-ids])]
    (is (= ["0:1" "0:3"] ids))
    (is (= [0.25 1.0 0.25] (mapv #(get-in changed [:instances % :system :opacity]) ["0:1" "0:2" "0:3"])))
    (is (= (mapv :params (vals (:instances show))) (mapv :params (vals (:instances changed)))))
    (is (= 2 (count (:events result))))
    (is (= changed (:model (model/apply-command changed cmd))))
    (is (empty? (:events (model/apply-command changed cmd))))
    (doseq [payload [{:selector {:instance-ids ["0:1" "missing"]} :action {:op :instance/remove}}
                     {:selector {} :action {:op :cue/launch}}
                     {:selector {:categories []} :action {:op :instance/opacity-set :value 2}}
                     {:selector {} :action {:op :instance/envelope-set :envelope {:release {:beats -1}}}}]]
      (let [bad (model/apply-command changed (command changed (assoc payload :op :group/apply)))]
        (is (= :rejected (get-in bad [:ack :status])))
        (is (identical? changed (:model bad)))))
    (is (= ["0:2"] (vec (keys (:instances (apply! changed {:op :group/apply :selector {:categories [:intensity]}
                                                          :action {:op :instance/remove}}))))))))

(deftest group-pause-and-restart-share-individual-lifecycle
  (let [paused (apply! (show) {:op :group/apply :selector {} :action {:op :instance/pause}})
        resumed (apply! paused {:op :group/apply :selector {:categories [:movement]} :action {:op :instance/resume}})
        restarted (apply! resumed {:op :show/restart})]
    (is (every? #(get-in % [:system :paused?]) (vals (:instances paused))))
    (is (= [true false true] (mapv #(get-in resumed [:instances % :system :paused?]) ["0:1" "0:2" "0:3"])))
    (is (= 1 (:epoch restarted)))
    (is (empty? (:instances restarted)))
    (is (= :stale-epoch (get-in (model/apply-command restarted (command paused {:op :instance/remove :instance-id "0:1"})) [:ack :code])))))

(deftest supplemental-emitters-report-the-color-category-on-every-control-surface
  (doseq [channel [:warm-white :cold-white :cool-white :cyan :lime :amber :uv]]
    (is (= [:color] (categories/definition-categories {:outputs {channel 1}})))
    (is (= [:color :intensity] (categories/definition-categories
                                 {:outputs [{:attribute channel} {:attribute :dimmer}]})))))

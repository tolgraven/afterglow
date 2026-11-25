(ns afterglow.control.views-test
  (:require [clojure.test :refer [deftest is]]
            [afterglow.control.devices.push-view :as push-view]
            [afterglow.control.display :as display]
            [afterglow.control.views :as views]))

(def show
  {:show-id :main :epoch 2 :revision 5 :time-ms 100 :master 0.8 :blackout? false
   :transport {:bpm 120 :playing? true} :private-key "not-published"
   :registry {:cues {:red {:id :red :effect-id :wash :version 1 :color [1 0 0]}
                     :blue {:id :blue :effect-id :wash :version 1 :color [0 0 1]}}}
   :pages {:main {:id :main :cells {[0 0] :red [1 1] :blue}}}
   :instances {"a" {:id "a" :cue-id :red :effect-id :wash :priority 1 :order 0
                      :phase :running :params {:color [0.5 0 0]} :definition {:secret "not-published"}}
               "b" {:id "b" :cue-id :red :effect-id :wash :priority 0 :order 1
                      :phase :releasing :params {}}}})

(deftest projections-preserve-semantic-order-and-cue-state
  (is (= ["b" "a"] (mapv :id (views/active-instances show))))
  (is (= ["b" "a"] (:instances (views/cue-view show :red))))
  (is (= [0.5 0 0] (:color (views/cue-view show :red))))
  (is (true? (:active? (views/cue-view show :red))))
  (is (false? (:releasing? (views/cue-view show :red))))
  (is (false? (:active? (views/cue-view show :blue))))
  (is (nil? (views/cue-view show :missing)))
  (is (= [[1 1] [0 0]] (mapv (juxt :x :y) (:cells (views/page-view show :main))))))

(deftest grouped-instances-preserve-cue-and-pad-projections
  (let [index (group-by :cue-id (views/active-instances show))]
    (doseq [view [views/cue-view views/pad-view] id [:red :blue :missing]]
      (let [expected (view show id)]
        (with-redefs [views/active-instances (fn [_] (throw (ex-info "Unexpected sort" {})))]
          (is (= expected (view show id index))))))))

(deftest public-snapshot-excludes-private-model-and-definition-fields
  (let [snapshot (views/snapshot show)]
    (is (= 5 (:revision snapshot)))
    (is (not (contains? snapshot :private-key)))
    (is (every? #(not (contains? % :definition)) (:instances snapshot)))
    (is (= [:blue :red] (mapv :id (:cues snapshot))))))

(deftest diffs-distinguish-missing-nil-and-removal
  (is (= {:set {:a nil :c 3} :remove [:b]}
         (views/diff-view {:b 2} {:a nil :c 3}))))

(deftest push-mixer-uses-exact-live-instances-and-bounds-each-page
  (let [instance (fn [n] (let [id (str "effect-" n)]
                          [id {:id id :cue-id :blue :effect-id :wash :priority 2 :order n :phase :running}]))
        model (-> show
                  (assoc-in [:registry :cues :red :name] "Red wash")
                  (assoc-in [:instances "a" :definition :params :level] {:type :number :bounds [0 1]})
                  (assoc-in [:instances "a" :params :level] 0.3)
                  (assoc-in [:instances "a" :system] {:opacity 0.25 :paused? true})
                  (assoc-in [:instances "b" :system :opacity] 0.6)
                  (assoc ::views/pad-colors {:red [0 1 0]})
                  (update :instances into (map instance (range 9))))
        state {:display-mode :mixer :page-id :main :origin [0 0] :selected-instance "b"
               :selected-cue :red :mixer-touches ["b" "a"]}
        project (fn [s] (:mixer (push-view/view s model (push-view/cue-index model) {})))
        page (project state)
        next-state (display/apply-action state model :display/mixer-next-page)]
    (is (= ["b" "a" "effect-0" "effect-1" "effect-2" "effect-3" "effect-4" "effect-5"]
           (mapv :id (:slots page))))
    (is (= {:name "Red wash" :phase :running :opacity 0.25 :paused? true :color [0.5 0 0]}
           (select-keys (second (:slots page)) [:name :phase :opacity :paused? :color])))
    (is (= {:phase :releasing :opacity 0.6 :color [1 0 0]}
           (select-keys (first (:slots page)) [:phase :opacity :color])))
    (is (= "b" (:selected-instance-id page)))
    (is (= "a" (get-in page [:expanded :instance-id])))
    (is (= [[:level 0.3]] (mapv (juxt :id :value) (get-in page [:expanded :parameters]))))
    (is (= "b" (get-in (project (assoc state :mixer-touches ["b"])) [:expanded :instance-id])))
    (is (nil? (:expanded (project (dissoc state :mixer-touches)))))
    (is (nil? (:expanded (project next-state))))
    (is (= ["effect-6" "effect-7" "effect-8"] (mapv :id (:slots (project next-state)))))
    (is (= {:page 1 :pages 2 :count 11} (select-keys (project next-state) [:page :pages :count])))
    (is (= next-state (display/apply-action next-state model :display/mixer-next-page)))
    (is (= 0 (:page (project (display/apply-action next-state model :display/mixer-previous-page)))))
    (is (= 1 (:page (project (assoc state :selected-instance "effect-7")))))
    (is (not (display/action-supported? {:display-capabilities display/parameter-only-capabilities} :display/mixer-next-page)))
    (is (= :mixer (display/mode {} (assoc-in model [:settings :controllers :push-display :mode] :mixer))))))

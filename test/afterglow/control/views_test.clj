(ns afterglow.control.views-test
  (:require [clojure.test :refer [deftest is]]
            [afterglow.control.model :as model]
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

(deftest partial-instances-sort-before-numeric-priorities
  (let [partial-show (model/new-show (update-in show [:instances "a"] dissoc :priority))
        ids ["a" "b"]]
    (is (= ids (mapv :id (views/active-instances partial-show))))
    (is (= ids (:instances (views/cue-view partial-show :red))))
    (is (= ids (mapv :id (:instances (views/snapshot partial-show)))))))

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

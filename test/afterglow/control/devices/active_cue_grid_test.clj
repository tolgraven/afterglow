(ns afterglow.control.devices.active-cue-grid-test
  (:require [afterglow.control.devices.active-cue-grid :as grid]
            [afterglow.control.model :as control]
            [afterglow.control.views :as views]
            [clojure.test :refer [deftest is]]))

(defn- empty-show []
  (control/new-show {:registry {:effects {:wash {:id :wash :version 1
                                                :params {:color {:type :color :default [1 0 0]}}}}
                               :cues {:warm {:id :warm :version 1 :effect-id :wash :name "Warm"}}}}))

(defn- command [show fields]
  (control/apply-command show
    (merge {:show-id (:show-id show) :epoch (:epoch show) :time-ms (:time-ms show)
            :source {:adapter :test} :command-id (str (:revision show))} fields)))

(defn- apply! [show fields]
  (let [result (command show fields)]
    (when-not (= :accepted (get-in result [:ack :status]))
      (throw (ex-info "Test command was rejected" (:ack result))))
    (:model result)))

(defn- launch [show & [source options]]
  (apply! show (cond-> {:op :cue/launch :cue-id :warm :launch (or options {})}
                 source (assoc :source source))))

(defn- published [state model]
  (grid/capture state (grid/project state model)))

(defn- cells [state model]
  (get-in (grid/project state model) [:view :cells]))

(deftest selection-uses-each-activation-and-projects-its-own-color
  (let [show (-> (empty-show)
                 (apply! {:op :page/put :page {:id :a :cells {[1 0] :warm}}})
                 (apply! {:op :page/put :page {:id :b :cells {[2 0] :warm}}})
                 (launch {:adapter :test :page-id :a} {:params {:color [1 0 0]}})
                 (launch {:adapter :test :page-id :b} {:params {:color [0 1 0]}}))
        state (published (grid/set-mode grid/initial-state :select) show)
        first-pad (grid/press state show :pad-a [0 0])
        second-pad (grid/press (:state first-pad) show :pad-b [1 0])
        closed (grid/set-mode (:state second-pad) nil)
        released (grid/release closed :pad-b)]
    (is (= ["0:1" "0:2"] (mapv :instance-id (cells state show))))
    (is (= [[:warm :wash 1 "Warm"] [:warm :wash 1 "Warm"]]
           (mapv (juxt :cue-id :effect-id :effect-version :name) (cells state show))))
    (is (= [[1 0 0] [0 1 0]] (mapv :color (cells state show))))
    (is (= [[0.1 0.2 0.3] [0.1 0.2 0.3]]
           (mapv :color (cells state (assoc show ::views/pad-colors {:warm [0.1 0.2 0.3]})))))
    (is (= [{:instance-id "0:1" :cue-id :warm} {:instance-id "0:2" :cue-id :warm}]
           (mapv :selection [first-pad second-pad])))
    (is (every? #(and (:handled? %) (empty? (:commands %))) [first-pad second-pad released]))
    (is (= {:state closed :handled? true :commands []} (grid/press closed show :pad-b [0 0])))
    (is (false? (:handled? (grid/release (:state released) :pad-b))))
    (is (false? (:handled? (grid/press (:state released) show :pad-b [0 0]))))
    (let [deleted (apply! show {:op :cue/delete :cue-id :warm})]
      (is (= [["0:1" :warm [1 0 0]] ["0:2" :warm [0 1 0]]]
             (mapv (juxt :instance-id :cue-id :color) (cells state deleted)))))))

(deftest reorder-across-pages-submits-one-captured-operation-and-shows-the-result
  (let [show (nth (iterate launch (empty-show)) 66)
        mode (grid/set-mode grid/initial-state :reorder)
        first-page (grid/project mode show)
        start (grid/press (grid/capture mode first-page) show :source [0 0])
        paged (grid/step-page (:state start) show 1)
        waiting (grid/press (grid/capture paged first-page) show :target [0 0])
        next-page (published (:state (grid/release (:state waiting) :target)) show)
        move (grid/press next-page show :target [0 0])
        expected {:op :instance/move-after :instance-id "0:1" :after-instance-id "0:65"
                  :show-id (:show-id show) :epoch (:epoch show) :expected-revision (:revision show)}
        moved (apply! show expected)]
    (is (= {:page 0 :page-count 2 :instance-count 66}
           (select-keys (:view first-page) [:page :page-count :instance-count])))
    (is (= [[0 0 "0:1"] [7 7 "0:64"]]
           (mapv (juxt :x :y :instance-id) ((juxt first peek) (get-in first-page [:view :cells])))))
    (is (= "0:1" (get-in (grid/project next-page show) [:view :source-instance-id])))
    (is (= paged (grid/capture paged first-page)))
    (is (every? #(and (:handled? %) (empty? (:commands %)) (nil? (:selection %))) [start waiting]))
    (is (every? #(nil? (:selection %)) [start waiting move]))
    (is (= [expected] (:commands move)))
    (is (= ["0:1" "0:66"] (mapv :instance-id (cells (:state move) moved))))
    (is (empty? (:commands (grid/release (:state move) :target))))
    (is (= 1 (:page (grid/step-page next-page show 1))))
    (let [reduced (update moved :instances dissoc "0:1" "0:66")]
      (is (= 0 (:page (published next-page reduced)))))))

(deftest active-order-and-release-changes-cannot-retarget-a-captured-press
  (let [show (nth (iterate launch (empty-show)) 4)
        state (published (grid/set-mode grid/initial-state :reorder) show)
        source (:state (grid/press state show :a [0 0]))
        external (apply! show {:op :instance/move-after :instance-id "0:1" :after-instance-id "0:3"})
        releasing (assoc-in show [:instances "0:2" :phase] :releasing)
        next-epoch (update show :epoch inc)
        fresh (published source external)
        new-source (grid/press fresh external :b [1 0])]
    (doseq [changed [external releasing next-epoch]]
      (let [stale (grid/press source changed :b [1 0])]
        (is (:handled? stale))
        (is (empty? (:commands stale)))
        (is (nil? (:selection stale)))))
    (is (= ["0:2" "0:3" "0:1" "0:4"] (mapv :instance-id (cells fresh external))))
    (is (= ["0:1" "0:3" "0:4"] (mapv :instance-id (cells source releasing))))
    (is (nil? (get-in (grid/project fresh external) [:view :source-instance-id])))
    (is (= "0:3" (get-in (grid/project (:state new-source) external) [:view :source-instance-id])))
    (is (empty? (:commands new-source)))
    (let [move (first (:commands (grid/press source show :b [1 0])))]
      (is (= :stale-revision (get-in (command external move) [:ack :code]))))))

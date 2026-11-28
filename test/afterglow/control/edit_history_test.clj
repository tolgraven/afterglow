(ns afterglow.control.edit-history-test
  (:require [afterglow.control.edit-history :as history]
            [clojure.test :refer [deftest is testing]]))

(def level [:instance-param "1:1" :level])

(def speed [:instance-param "1:1" :speed])

(def push-level {:actor "push" :control-id "encoder-1" :target level :gesture-id "level-1"})

(def studio-speed {:actor "studio" :control-id "slider" :target speed :gesture-id "speed-1"})

(defn- new-show [limit]
  {:history (history/new-history limit)
   :targets {level {:value 0.2 :generation 0} speed {:value 20 :generation 0}}})

(defn- propose [{:keys [history targets]} command]
  (history/apply-action history targets command))

(defn- apply! [show command]
  (let [{:keys [status history writes] :as result} (propose show command)]
    (is (= :accepted status) (pr-str (select-keys result [:status :code :target])))
    (reduce-kv (fn [show target value] (assoc-in show [:targets target :value] value))
               (assoc show :history history) writes)))

(defn- gesture [show operation identity & [fields]]
  (apply! show (assoc (merge identity fields) :op operation)))

(defn- sample [show identity sequence value]
  (gesture show :gesture/sample identity {:sequence sequence :value value}))

(defn- edit [show identity value]
  (-> show
      (gesture :gesture/begin identity)
      (sample identity 1 value)
      (gesture :gesture/end identity {:last-sequence 1})))

(defn- navigation [{:keys [history]} op & [node-id]]
  {:op op :expected-cursor (:cursor history) :expected-history-position (history/position history) :node-id node-id})

(defn- navigate [show op & [node-id]]
  (apply! show (navigation show op node-id)))

(deftest live-samples-commit-once
  (let [before (new-show 16)
        started (gesture before :gesture/begin push-level)
        samples (rest (reductions (fn [show i] (sample show push-level i (/ i 100.0)))
                                  started (range 1 81)))
        sampled (last samples)
        ended (gesture sampled :gesture/end push-level {:last-sequence 80})]
    (is (= (map #(/ % 100.0) (range 1 81))
           (map #(get-in % [:targets level :value]) samples)))
    (is (= 0 (get-in sampled [:history :cursor])))
    (is (= 0 (history/position (:history sampled))))
    (is (= {:parent 0 :target level :actor "push" :control-id "encoder-1"
            :before 0.2 :after 0.8 :generation 0}
           (get-in ended [:history :nodes 1])))
    (is (= 1 (get-in ended [:history :cursor])))
    (is (= 1 (history/position (:history ended))))
    (is (= 2 (count (get-in ended [:history :nodes]))))
    (is (empty? (get-in ended [:history :open])))
    (doseq [sequence [79 80]]
      (let [result (propose sampled (assoc push-level :op :gesture/sample :sequence sequence :value 0.9))]
        (is (= :stale-sample (:code result)))
        (is (identical? (:history sampled) (:history result)))
        (is (empty? (:writes result)))))
    (is (= :stale-gesture-end (:code (propose sampled (assoc push-level :op :gesture/end :last-sequence 79)))))
    (is (= :unknown-gesture (:code (propose ended (assoc push-level :op :gesture/end :last-sequence 80)))))))

(deftest alternate-branches-and-cursor
  (let [one (edit (new-show 16) push-level 0.5)
        root (navigate one :history/undo)
        alternate (edit root (assoc push-level :gesture-id "level-2" :actor "studio") 0.8)
        original (navigate alternate :history/select 1)
        undone (navigate original :history/undo)
        redone (navigate undone :history/redo 2)]
    (is (= 0.2 (get-in root [:targets level :value])))
    (is (= [0 0] (mapv #(get-in alternate [:history :nodes % :parent]) [1 2])))
    (is (= 1 (get-in original [:history :cursor])))
    (is (= 0.5 (get-in original [:targets level :value])))
    (is (= 2 (get-in redone [:history :cursor])))
    (is (= 0.8 (get-in redone [:targets level :value])))
    (is (= (:nodes (:history alternate)) (:nodes (:history redone))))
    (is (= [1 2 3 4 5 6] (mapv #(history/position (:history %)) [one root alternate original undone redone])))
    (is (= :stale-history-cursor (:code (propose redone (navigation original :history/undo)))))
    (is (= :stale-history-position (:code (propose redone (navigation alternate :history/undo)))))
    (is (= :not-a-history-child (:code (propose redone (navigation redone :history/redo 1)))))))

(deftest switching-equivalent-branches-only-moves-the-cursor
  (let [original (edit (new-show 16) push-level 0.5)
        alternate (edit (navigate original :history/undo)
                        (assoc push-level :gesture-id "other") 0.5)
        result (propose alternate (navigation alternate :history/select 1))]
    (is (= :accepted (:status result)))
    (is (= 1 (get-in result [:history :cursor])))
    (is (empty? (:writes result)))))

(deftest concurrent-gestures-cancel-and-no-op
  (let [started (-> (new-show 16)
                    (gesture :gesture/begin push-level)
                    (gesture :gesture/begin studio-speed))
        changed (-> started (sample push-level 1 0.9) (sample studio-speed 1 40))
        cancelled (gesture changed :gesture/cancel push-level)
        ended (gesture cancelled :gesture/end studio-speed {:last-sequence 1})
        no-op (-> ended
                  (gesture :gesture/begin push-level)
                  (sample push-level 1 0.6)
                  (sample push-level 2 0.2)
                  (gesture :gesture/end push-level {:last-sequence 2}))]
    (is (= :gesture-active (:code (propose started (assoc push-level :op :gesture/begin :gesture-id "other")))))
    (is (= :unknown-gesture (:code (propose changed (assoc push-level :op :gesture/cancel :actor "other")))))
    (is (= :invalid-value (:code (propose changed (assoc push-level :op :gesture/sample :sequence 2 :value Double/NaN)))))
    (is (= 0.2 (get-in cancelled [:targets level :value])))
    (is (= 40 (get-in cancelled [:targets speed :value])))
    (is (= speed (get-in ended [:history :nodes 1 :target])))
    (is (= (:history ended) (:history no-op)))))

(deftest conflict-is-target-scoped-and-travel-is-atomic
  (let [edited (-> (new-show 16) (edit push-level 0.7) (edit studio-speed 60))
        externally-written (-> edited
                               (assoc-in [:targets level] {:value 0.5 :generation 1})
                               (assoc-in [:targets level] {:value 0.7 :generation 2}))
        failed (propose externally-written (navigation externally-written :history/select 0))
        undone (navigate externally-written :history/undo)]
    (testing "A generation change catches another writer even when the observed value matches"
      (is (= :history-conflict (:code failed)))
      (is (= level (:target failed)))
      (is (identical? (:history externally-written) (:history failed)))
      (is (empty? (:writes failed))))
    (testing "A different target can still be undone"
      (is (= 20 (get-in undone [:targets speed :value])))
      (is (= 0.7 (get-in undone [:targets level :value])))
      (is (= 1 (get-in undone [:history :cursor])))
      (is (= :history-conflict (:code (propose undone (navigation undone :history/undo))))))
    (testing "A missing instance target cannot be revived by history"
      (is (= :target-unavailable
             (:code (propose (update undone :targets dissoc level)
                             (navigation undone :history/undo))))))
    (testing "A differing value at the expected generation is also a conflict"
      (is (= :history-conflict
             (:code (propose (assoc-in edited [:targets speed :value] 63)
                             (navigation edited :history/undo))))))))

(deftest conflicting-gesture-cannot-finish-or-roll-back-an-external-write
  (let [changed (-> (new-show 16) (gesture :gesture/begin push-level) (sample push-level 1 0.9))
        overwritten (assoc-in changed [:targets level] {:value 0.4 :generation 1})
        ended (propose overwritten (assoc push-level :op :gesture/end :last-sequence 1))
        cancelled (propose overwritten (assoc push-level :op :gesture/cancel))]
    (is (= :history-conflict (:code (propose overwritten (assoc push-level :op :gesture/sample :sequence 2 :value 0.6)))))
    (doseq [{:keys [status discarded writes history]} [ended cancelled]]
      (is (= :accepted status))
      (is (= :history-conflict discarded))
      (is (empty? writes))
      (is (empty? (:open history)))
      (is (= 0 (:cursor history))))))

(deftest bounded-pruning-preserves-current-ancestry
  (let [base (edit (new-show 4) push-level 0.4)
        older (edit base (assoc push-level :gesture-id "level-2") 0.5)
        middle (edit (navigate older :history/undo) (assoc push-level :gesture-id "level-3") 0.6)
        newest (edit (navigate middle :history/undo) (assoc push-level :gesture-id "level-4") 0.7)
        next (edit newest (assoc push-level :gesture-id "level-5") 0.8)
        rolled (edit next (assoc push-level :gesture-id "level-6") 0.9)
        boundary (navigate rolled :history/select 1)]
    (is (= #{0 1 3 4} (set (keys (get-in newest [:history :nodes])))))
    (is (= #{0 1 4 5} (set (keys (get-in next [:history :nodes])))))
    (is (= #{1 4 5 6} (set (keys (get-in rolled [:history :nodes])))))
    (is (= {:parent nil} (get-in rolled [:history :nodes 1])))
    (is (= 6 (get-in rolled [:history :cursor])))
    (is (= 0.4 (get-in boundary [:targets level :value])))
    (is (= :at-history-root (:code (propose boundary (navigation boundary :history/undo)))))))

(def staged [:staged-param "s" :level])

(def staged-level {:actor "studio" :control-id "stage" :target staged :gesture-id "staged-1"})

(defn- with-staged [show value]
  (assoc-in show [:targets staged] {:value value :generation 0}))

(deftest removing-targets-splices-their-edits-and-keeps-travel-valid
  (let [show (-> (new-show 16) (with-staged 0.7)
                 (edit push-level 0.4)                                        ; 1
                 (edit staged-level 0.3)                                      ; 2
                 (edit (assoc push-level :gesture-id "level-2") 0.5))         ; 3, child of the staged edit
        branched (-> show (navigate :history/undo) (navigate :history/undo)
                     (edit (assoc push-level :gesture-id "level-3") 0.6))     ; 4, from 1
        removed (history/remove-targets (:history branched) [staged])
        spliced (assoc branched :history removed :targets (dissoc (:targets branched) staged))]
    (testing "children attach to the nearest remaining ancestor and IDs keep their order"
      (is (= {0 nil 1 0 3 1 4 1} (update-vals (:nodes removed) :parent)))
      (is (every? (fn [[id {:keys [parent]}]] (or (nil? parent) (< parent id))) (:nodes removed)))
      (is (= 4 (:cursor removed)))
      (is (= (inc (history/position (:history branched))) (history/position removed)))
      (is (not (contains? (:generations removed) staged)))
      (is (not (contains? (history/tracked-targets removed) staged))))
    (testing "travel computed against the old tree is refused"
      (is (= :stale-history-position (:code (propose spliced (navigation branched :history/undo))))))
    (testing "the spliced tree still travels and redoes into the reattached edit"
      (let [undone (navigate spliced :history/undo)
            redone (navigate undone :history/redo 3)]
        (is (= 0.4 (get-in undone [:targets level :value])))
        (is (= 0.5 (get-in redone [:targets level :value])))))
    (testing "a cursor on a removed edit moves to its ancestor"
      (let [at-staged (navigate (navigate show :history/undo) :history/select 2)]
        (is (= 1 (:cursor (history/remove-targets (:history at-staged) [staged]))))))
    (testing "an untracked target changes nothing"
      (is (identical? removed (history/remove-targets removed [[:staged-param "other" :level]]))))
    (testing "an open gesture on a removed target is dropped"
      (let [open (gesture (with-staged (new-show 4) 0.7) :gesture/begin staged-level)]
        (is (= {staged {:actor "studio" :control-id "stage" :gesture-id "staged-1" :last-sequence 0}}
               (history/open-gestures (:history open))))
        (is (= {} (:open (history/remove-targets (:history open) [staged]))))))
    (testing "pruning after a splice keeps a single root"
      (let [bounded (reduce (fn [show n] (edit show (assoc push-level :gesture-id (str "p" n)) (/ n 10.0)))
                            (assoc spliced :history (assoc removed :limit 4)) (range 1 6))]
        (is (= 1 (count (filter #(= {:parent nil} %) (vals (get-in bounded [:history :nodes]))))))
        (is (<= (count (get-in bounded [:history :nodes])) 4))))))

(deftest retargeting-moves-edits-to-a-new-owner
  (let [show (-> (new-show 8) (with-staged 0.7) (edit staged-level 0.3) (edit (assoc staged-level :gesture-id "staged-2") 0.35))
        moved-target [:instance-param "1:2" :level]
        moved (history/retarget (:history show) staged moved-target)
        launched (-> show (assoc :history moved)
                     (update :targets #(-> % (dissoc staged) (assoc moved-target (get % staged)))))]
    (is (= [moved-target moved-target] (keep :target (vals (:nodes moved)))))
    (is (= {moved-target 3} (:generations (history/retarget (assoc (:history show) :generations {staged 3})
                                                            staged moved-target))))
    (is (= (select-keys (:history show) [:cursor :position :next-id]) (select-keys moved [:cursor :position :next-id])))
    (is (= 0.3 (get-in (navigate launched :history/undo) [:targets moved-target :value])))
    (is (thrown? clojure.lang.ExceptionInfo (history/retarget moved staged moved-target)))))

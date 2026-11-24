(ns afterglow.control.edit-history
  "Pure scalar parameter gesture and branching history transitions.")

(def ^:private open-limit 32)

(defn new-history
  "The limit includes the root. Parent links and node IDs survive navigation."
  [limit]
  (when-not (and (integer? limit) (<= 2 limit))
    (throw (ex-info "Edit history needs room for a root and one edit" {:limit limit})))
  {:limit limit :next-id 1 :cursor 0 :nodes {0 {:parent nil}} :open {}})

(defn- accepted [history writes]
  {:status :accepted :history history :writes writes})

(defn- rejected [history code & [target]]
  (cond-> {:status :rejected :history history :writes {} :code code}
    target (assoc :target target)))

(defn- finite-number? [value]
  (and (number? value) (Double/isFinite (double value))))

(defn- canonical [targets target]
  (let [{:keys [value generation] :as cell} (get targets target)]
    (when (and (finite-number? value) (integer? generation) (<= 0 generation))
      cell)))

(defn- current? [cell generation value]
  (and cell (= generation (:generation cell)) (= value (:value cell))))

(defn- prune [{:keys [limit nodes cursor] :as history}]
  (if (<= (count nodes) limit)
    history
    (let [oldest-first (sort (keys nodes))
          parents (into #{} (keep :parent) (vals nodes))
          alternate (first (remove #(or (= cursor %) (contains? parents %)) oldest-first))]
      (if (some? alternate)
        (update history :nodes dissoc alternate)
        (let [[root next-root] oldest-first]
          (assoc history :nodes (-> nodes
                                    (dissoc root)
                                    (assoc next-root {:parent nil}))))))))

(defn- record-edit [{:keys [cursor next-id] :as history}
                    target {:keys [actor control-id before after generation]}]
  (prune (-> history
             (assoc-in [:nodes next-id] {:parent cursor :target target :actor actor
                                        :control-id control-id :before before :after after
                                        :generation generation})
             (assoc :cursor next-id :next-id (inc next-id)))))

(defn- gesture-owner [action]
  (mapv action [:actor :control-id :gesture-id]))

(defn- start-gesture [history targets {:keys [target] :as action}]
  (let [cell (canonical targets target)
        [actor control-id gesture-id :as owner] (gesture-owner action)]
    (cond
      (some nil? owner) (rejected history :invalid-gesture target)
      (nil? cell) (rejected history :target-unavailable target)
      (get-in history [:open target]) (rejected history :gesture-active target)
      (>= (count (:open history)) open-limit) (rejected history :too-many-gestures target)
      :else (accepted (assoc-in history [:open target]
                                {:actor actor :control-id control-id :gesture-id gesture-id
                                 :before (:value cell) :after (:value cell)
                                 :generation (:generation cell) :last-sequence 0}) {}))))

(defn- gesture-action
  [history targets {:keys [op target value sequence last-sequence] :as action}]
  (let [{:keys [before after generation] :as gesture} (get-in history [:open target])
        cell (canonical targets target)
        owned-value? (current? cell generation after)]
    (cond
      (or (nil? gesture) (not= (gesture-owner action) (gesture-owner gesture)))
      (rejected history :unknown-gesture target)

      (= :gesture/sample op)
      (cond
        (not owned-value?) (rejected history :history-conflict target)
        (not (and (integer? sequence) (> sequence (:last-sequence gesture))))
        (rejected history :stale-sample target)
        (not (finite-number? value)) (rejected history :invalid-value target)
        :else (accepted (update-in history [:open target] assoc :after value :last-sequence sequence)
                        (if (= after value) {} {target value})))

      (and (= :gesture/end op) (not= last-sequence (:last-sequence gesture)))
      (rejected history :stale-gesture-end target)

      :else
      (let [closed (update history :open dissoc target)]
        (cond
          (not owned-value?) (assoc (accepted closed {}) :discarded :history-conflict)
          (= before after) (accepted closed {})
          (= :gesture/cancel op) (accepted closed {target before})
          :else (accepted (record-edit closed target gesture) {}))))))

(defn- lineage [nodes start]
  (loop [id start, path []]
    (if (nil? id) path
        (recur (get-in nodes [id :parent]) (conj path id)))))

(defn- travel [{:keys [cursor nodes] :as history} targets destination]
  (let [from (lineage nodes cursor)
        to (lineage nodes destination)
        ancestor (first (filter (set to) from))
        backward (take-while #(not= ancestor %) from)
        forward (reverse (take-while #(not= ancestor %) to))
        steps (concat (map #(vector % :after :before) backward)
                      (map #(vector % :before :after) forward))]
    (loop [remaining steps, values {}]
      (if-let [[id read-key write-key] (first remaining)]
        (let [{:keys [target generation] :as node} (get nodes id)
              cell (canonical targets target)
              value (get values target (:value cell))]
          (cond
            (nil? cell) (rejected history :target-unavailable target)
            (get-in history [:open target]) (rejected history :gesture-active target)
            (or (not= generation (:generation cell)) (not= (get node read-key) value))
            (rejected history :history-conflict target)
            :else (recur (next remaining) (assoc values target (get node write-key)))))
        (accepted (assoc history :cursor destination)
                  (into {} (remove (fn [[target value]] (= value (get-in targets [target :value]))))
                        values))))))

(defn- navigate [{:keys [cursor nodes] :as history} targets
                 {:keys [op expected-cursor node-id]}]
  (let [parent (get-in nodes [cursor :parent])]
    (cond
      (not= cursor expected-cursor) (rejected history :stale-history-cursor)
      (= :history/undo op) (if (nil? parent) (rejected history :at-history-root)
                              (travel history targets parent))
      (not (contains? nodes node-id)) (rejected history :unknown-history-node)
      (and (= :history/redo op) (not= cursor (get-in nodes [node-id :parent])))
      (rejected history :not-a-history-child)
      :else (travel history targets node-id))))

(defn apply-action
  "Return next history and canonical writes for one admitted action. Commit both
  together through the show reducer, after validating all writes against current
  schemas. The caller supplies live scalar cells keyed by target, each with
  :value and :generation. Advance the generation for canonical value changes
  outside these actions, keeping generations with live targets. The caller
  normalizes scalar values to their schema's numeric type for exact comparison.

  The caller owns authentication, command receipts and deadline scheduling. The
  :open map belongs to the live show epoch and is excluded from saved history. Use
  a history created here or separately validated on import, with acyclic parents.
  Begin, sample, end and cancel use a stable trusted :actor, :control-id,
  :gesture-id and :target. Samples require increasing :sequence values. End
  requires :last-sequence from the final accepted sample, or zero for no samples.
  Undo, redo and select require :expected-cursor. Redo and select use :node-id."
  [history targets {:keys [op] :as action}]
  (case op
    :gesture/begin (start-gesture history targets action)
    (:gesture/sample :gesture/end :gesture/cancel) (gesture-action history targets action)
    (:history/undo :history/redo :history/select) (navigate history targets action)
    (rejected history :unknown-history-operation)))

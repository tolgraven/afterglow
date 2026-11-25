(ns afterglow.render.coverage
  "Plan physical typed writes after ordered native layers have composed."
  (:require [afterglow.render.layers :as layers])
  (:import [java.util BitSet]))

(defn- index-overlap? [^BitSet targets ^ints indices]
  (loop [row 0]
    (when (< row (alength indices))
      (or (.get targets (aget indices row)) (recur (inc row))))))

(defn- as-targets ^BitSet [coverage]
  (if (instance? BitSet coverage)
    coverage
    (doto (BitSet.) (.set 0 (int coverage)))))

(defn- outside-prefix? [^ints indices ^long prefix]
  (loop [row 0]
    (when (< row (alength indices))
      (or (>= (aget indices row) prefix) (recur (inc row))))))

(defn- extend-targets [coverage ^ints indices rows]
  (cond
    (and (nil? indices) (number? coverage)) (max coverage rows)
    (and (nil? indices) (>= rows (.length ^BitSet coverage))) rows
    (and indices (number? coverage) (not (outside-prefix? indices (long coverage)))) coverage
    :else
    (let [^BitSet targets (if (instance? BitSet coverage)
                            (.clone ^BitSet coverage)
                            (as-targets coverage))]
      (if indices
        (dotimes [row rows] (.set targets (aget indices row)))
        (.set targets 0 (int rows)))
      targets)))

(defn- plan-column [column coverage ^ints indices rows]
  (if (or (zero? rows) (= 0 coverage)) column
    (if (and (nil? indices) (number? coverage))
      (assoc column ::validate-prefix (min rows coverage))
      (let [targets (as-targets coverage)]
        (if (if indices (index-overlap? targets indices) (< -1 (.nextSetBit targets 0) rows))
          (assoc column ::validate-targets targets)
          column)))))

(defn- plan-batch [block covered update-coverage?]
  (let [{:keys [target-indices target-ids blend opacity columns] :as batch} (:compiled block)
        rows (count target-ids)
        opaque? (and (= :replace blend) (== 1 opacity) (nil? (::layers/opacities batch)))]
    (if opaque?
      [(let [planned (reduce-kv (fn [result i {:keys [attribute slot] :as column}]
                                 (if slot
                                   (let [planned (plan-column column (get covered attribute 0) target-indices rows)]
                                     (if (identical? column planned) result (assoc result i planned)))
                                   result)) columns columns)]
         (if (identical? columns planned) block (assoc-in block [:compiled :columns] planned)))
       (if (and update-coverage? (pos? rows))
         (reduce (fn [m {:keys [attribute slot]}]
                   (if slot (update m attribute (fnil extend-targets 0) target-indices rows) m)) covered columns)
         covered)]
      ;; A partial or blended write may need the lower value, including to
      ;; report an intermediate out-of-range blend.
      [block (reduce #(dissoc %1 (:attribute %2)) covered columns)])))

(defn plan
  "Mark the targets of a physical typed column which are guaranteed to be
  overwritten. The renderer must still validate it at its original point in
  the stream. Uncompiled assignments are conservative dependency barriers."
  [blocks]
  (loop [i (dec (count blocks)) result blocks covered {}]
    (if (neg? i) result
      (let [block (nth blocks i)]
        (if (= :batch (:kind block))
          (let [[planned next-covered] (plan-batch block covered (pos? i))]
            (recur (dec i) (if (identical? planned block) result (assoc result i planned)) next-covered))
          (recur (dec i) result {}))))))

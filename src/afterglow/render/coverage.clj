(ns afterglow.render.coverage
  "Plan physical typed writes after ordered native layers have composed."
  (:require [afterglow.render.layers :as layers]))

(defn- plan-batch [block covered]
  (let [{:keys [target-indices target-ids blend opacity columns] :as batch} (:compiled block)
        prefix (count target-ids)
        opaque-prefix? (and (nil? target-indices) (= :replace blend) (== 1 opacity)
                            (nil? (::layers/opacities batch)))
        plan-column (fn [result i {:keys [attribute slot] :as column}]
                      (let [length (min prefix (long (get covered attribute 0)))]
                        (if (and slot (pos? length))
                          (assoc result i (assoc column ::validate-prefix length)) result)))]
    (if opaque-prefix?
      [(let [planned (reduce-kv plan-column columns columns)]
         (if (identical? columns planned) block (assoc-in block [:compiled :columns] planned)))
       (reduce (fn [m {:keys [attribute slot]}]
                 (if slot (update m attribute (fnil max 0) prefix) m)) covered columns)]
      ;; A partial, additive or arbitrarily indexed write may need the lower
      ;; value, including to report an intermediate out-of-range blend.
      [block (reduce #(dissoc %1 (:attribute %2)) covered columns)])))

(defn plan
  "Mark the prefix of a physical typed column which is guaranteed to be
  overwritten. The renderer must still validate it at its original point in
  the stream. Uncompiled assignments are conservative dependency barriers."
  [blocks]
  (loop [i (dec (count blocks)) result blocks covered {}]
    (if (neg? i) result
      (let [block (nth blocks i)]
        (if (= :batch (:kind block))
          (let [[planned next-covered] (plan-batch block covered)]
            (recur (dec i) (if (identical? planned block) result (assoc result i planned)) next-covered))
          (recur (dec i) result {}))))))

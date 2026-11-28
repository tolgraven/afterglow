(ns afterglow.control.bounded-test
  (:require [afterglow.control.bounded :as bounded]
            [clojure.test :refer [deftest is testing]]))

(defn- backing [order]
  (if (instance? clojure.lang.APersistentVector$SubVector order)
    (count (.v ^clojure.lang.APersistentVector$SubVector order))
    (count order)))

(deftest an-order-keeps-exactly-the-newest-entries
  (doseq [limit [1 2 5 33 1024]]
    (testing (str "limit " limit)
      (loop [i 0 order [] dropped-all []]
        (if (< i (* 3 (+ limit 40)))
          (let [[order dropped] (bounded/append order i limit)]
            (is (vector? order))
            (is (= (vec (take-last limit (range (inc i)))) order))
            (is (= (vec (take-last limit (range (inc i)))) (seq order)) "it reads as a sequence too")
            (is (= i (peek order)))
            (recur (inc i) order (into dropped-all dropped)))
          (is (= (vec (range (- i limit))) dropped-all) "every entry is dropped once, oldest first"))))))

(deftest trimming-copies-an-order-at-most-once-per-limit-appends
  ;; Before, every append past the limit copied the whole order: 8,976 copies
  ;; of 1,024 IDs for these 10,000 appends.
  (let [limit 1024
        copies (atom 0)
        order (reduce (fn [order i]
                        (let [[next-order] (bounded/append order i limit)]
                          (when (and (>= i limit) (not (instance? clojure.lang.APersistentVector$SubVector next-order)))
                            (swap! copies inc))
                          (is (<= (backing next-order) (+ 33 (* 2 limit))) "the retained vector stays bounded")
                          next-order))
                      [] (range 10000))]
    (is (= (vec (range (- 10000 limit) 10000)) order))
    (is (<= @copies (inc (quot 10000 limit))))
    (is (pos? @copies))))

(deftest dropping-nothing-returns-the-order
  (let [order [1 2 3]]
    (is (identical? order (bounded/drop-oldest order 0)))
    (is (= [3] (bounded/drop-oldest order 2)))
    (is (= [] (bounded/drop-oldest order 3)))))

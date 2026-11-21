(ns afterglow.core-test
  (:require [clojure.test :refer :all]
            [afterglow.show-context :refer [*show* with-show]]))

(deftest nested-show-contexts-restore-the-caller
  (with-show {:id :outer}
    (is (= :outer (:id *show*)))
    (is (= :inner (with-show {:id :inner} (:id *show*))))
    (is (= :outer (:id *show*)))))

(deftest failed-effect-does-not-leak-a-show-binding
  (with-show {:id :caller}
    (is (thrown-with-msg? Exception #"effect failed"
          (with-show {:id :effect}
            (throw (Exception. "effect failed")))))
    (is (= :caller (:id *show*)))))

(deftest concurrent-show-contexts-are-isolated
  (let [gate (promise)
        jobs (mapv (fn [id]
                     (with-show {:id id}
                       (future @gate (:id *show*))))
                   [:first :second])]
    (try
      (deliver gate true)
      (is (= [:first :second] (mapv #(deref % 5000 ::timeout) jobs)))
      (finally
        (doseq [job jobs] (future-cancel job))))))

(ns afterglow.control.devices.push-view-test
  (:require [clojure.test :refer [deftest is]]
            [afterglow.control.devices.push-view :as push-view]))

(deftest touched-parameters-are-capped-deduplicated-and-ordered-by-the-caller
  (let [entries (mapv #(hash-map :instance-id :a :param (keyword (str "p" %)) :component 0) (range 12))]
    (is (= (subvec entries 0 8) (push-view/touched-parameters entries)))
    (is (= [(entries 2) (entries 1)] (push-view/touched-parameters [nil (entries 2) (entries 1) (entries 2)])))
    (is (= [] (push-view/touched-parameters nil)))))

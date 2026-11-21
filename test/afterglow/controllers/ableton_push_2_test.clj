(ns afterglow.controllers.ableton-push-2-test
  (:require [afterglow.controllers :as controllers]
            [afterglow.controllers.ableton-push-2 :as push]
            [clojure.test :refer [deftest is]]))

(deftest loading-the-driver-registers-the-push-2
  (is (fn? (get @controllers/recognizers ::push/controller)))
  (is (contains? (methods controllers/bind-to-show-impl) ::push/controller))
  (is (contains? (methods controllers/deactivate) ::push/controller)))

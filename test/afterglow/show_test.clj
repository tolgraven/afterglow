(ns afterglow.show-test
  (:require [clojure.test :refer :all]
            [afterglow.effects :as fx]
            [afterglow.show :as show]
            [afterglow.show-context :refer [*show* with-show]]))

(use-fixtures :each
  (fn [f]
    ;; Construct the coordinator, but never start its renderer or output ports.
    (with-show (show/show)
      (f))))

(defn- active-keys []
  (mapv :key (:meta @(:active-effects *show*))))

(deftest priority-is-ascending-with-launch-order-breaking-ties
  (show/add-effect! :first (fx/blank "First") :priority 10)
  (show/add-effect! :low (fx/blank "Low") :priority -1)
  (show/add-effect! :second (fx/blank "Second") :priority 10)
  (show/add-effect! :middle (fx/blank "Middle") :priority 0)
  (is (= [:low :middle :first :second] (active-keys)))
  (is (= {:low 0 :middle 1 :first 2 :second 3}
         (:indices @(:active-effects *show*))))
  (is (false? (show/running?))))

(deftest replacement-gets-a-new-id-and-old-stop-cannot-end-it
  (let [old-id (show/add-effect! :pulse (fx/blank "Old"))]
    (show/add-effect! :other (fx/blank "Other"))
    (let [new-id (show/add-effect! :pulse (fx/blank "New"))]
      (is (< old-id new-id))
      (is (= [:other :pulse] (active-keys)))
      (show/end-effect! :pulse :when-id old-id)
      (is (= new-id (:id (show/find-effect :pulse))))
      (is (= "New" (get-in (show/find-effect :pulse) [:effect :name])))
      (show/end-effect! :pulse :when-id new-id)
      (is (nil? (show/find-effect :pulse)))
      (is (= [:other] (active-keys))))))

(deftest first-stop-begins-release-and-second-stop-forces-removal
  (let [end-calls (atom 0)
        releasing (fx/->Effect "Release" fx/always-active (fn [_ _] [])
                               (fn [_ _] (swap! end-calls inc) false))]
    (show/add-effect! :release releasing)
    (show/end-effect! :release)
    (is (:ending (show/find-effect :release)))
    (is (= 1 @end-calls))
    (show/end-effect! :release)
    (is (nil? (show/find-effect :release)))
    (is (= 1 @end-calls))
    (is (= {:effects [] :meta [] :indices {} :ending #{}}
           @(:active-effects *show*)))))

(deftest clearing-effects-resets-priority-indices-and-ending-state
  (show/add-effect! :one (fx/blank))
  (show/add-effect! :two (fx/blank) :priority 2)
  (show/clear-effects!)
  (is (= {:effects [] :meta [] :indices {} :ending #{}}
         @(:active-effects *show*)))
  (show/add-effect! :new (fx/blank))
  (is (= [:new] (active-keys)))
  (is (= {:new 0} (:indices @(:active-effects *show*)))))

(ns afterglow.show-test
  (:require [clojure.test :refer :all]
            [afterglow.channels :as channels]
            [afterglow.effects :as fx]
            [afterglow.show :as show]
            [afterglow.show-context :refer [*show* with-show]]
            [ola-clojure.ola-service :as ola])
  (:import [com.google.protobuf ByteString]))

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

(defn- capture-blackout [operation]
  (let [packets (atom [])]
    (with-redefs [ola/UpdateDmxData
                  (fn [{:keys [universe ^ByteString data]} callback]
                    (swap! packets conj
                           [universe (.size data)
                            (into {} (keep-indexed (fn [index value]
                                                    (when-not (zero? value)
                                                      [(inc index) (bit-and 255 value)]))
                                                  (.toByteArray data)))
                            callback]))]
      (operation))
    (sort-by first @packets)))

(deftest legacy-show-blackout-packs-patched-emission-darkness
  (with-show (show/show :universes [1 2])
    (show/patch-fixture! :head {:name "Mixed output"
                               :channels [(channels/dimmer 1)
                                          (channels/dimmer 2 :inverted-from 0)
                                          (channels/dimmer 3 :inverted-from 32)
                                          (assoc (channels/fine-channel :pan 4) :inverted-from 0)
                                          (assoc (channels/fine-channel :fog 6) :inverted-from 0)]
                               :heads [{:x 0 :y 0 :z 0
                                        :channels [(assoc (channels/color 5 :red) :inverted-from 0)]}]}
                         1 1)
    (show/patch-fixture! :fine-dimmer {:name "Fine inverted dimmer"
                                      :channels [(channels/dimmer 1 :fine-offset 2 :inverted-from 0)]}
                         1 511)
    (is (= [[1 512 {2 255, 5 255, 511 255} nil]
            [2 512 {} nil]]
           (capture-blackout show/blackout-show)))
    (is (= [[1 512 {} nil]] (capture-blackout #(show/blackout-universe 1))))))

(deftest legacy-shutdown-blacks-out-patched-fixtures
  (show/patch-fixture! :dimmer {:name "Inverted dimmer"
                               :channels [(channels/dimmer 1 :inverted-from 0)]}
                       1 512)
  (let [active (atom #{*show*})]
    (with-redefs [show/active-shows active]
      (is (= [[1 512 {512 255} nil]] (capture-blackout show/stop-all!)))
      (is (empty? @active)))))

(deftest legacy-patch-rejects-addresses-used-by-fixture-heads
  (with-show (show/show :universes [1 2])
    (let [head-only {:name "Head-only dimmer"
                     :heads [{:x 0 :y 0 :z 0 :channels []}
                             {:x 0 :y 0 :z 0 :channels [(channels/dimmer 1 :fine-offset 2)]}]}
          fog {:name "Fog" :channels [(channels/fine-channel :fog 1)]}]
      (show/patch-fixture! :head-only head-only 1 20)
      (is (= {1 {20 :head-only 21 :head-only} 2 {}} (show/address-map)))
      (is (thrown-with-msg? IllegalStateException #"Channel 21 in use by fixture :head-only"
                            (show/patch-fixture! :fog fog 1 21)))
      (is (= :other-universe (show/patch-fixture! :other-universe fog 2 21)))
      (is (thrown-with-msg? IllegalStateException #"Channel 21 in use by fixture :other-universe"
                            (show/patch-fixture! :overlapping-head head-only 2 20))))))

(deftest legacy-blackout-zeroes-ambiguous-slots
  (show/patch-fixture! :pan {:name "Pan" :channels [(channels/fine-channel :pan 1)]} 1 2)
  (show/patch-fixture! :fog {:name "Fog" :channels [(channels/fine-channel :fog 1)]} 1 3)
  (show/patch-fixture! :lamp {:name "Inverted dimmer" :channels [(channels/dimmer 1 :inverted-from 0)]} 1 4)
  (let [old-fixture {:name "Older overlapping fixture"
                     :channels [(channels/dimmer 1 :fine-offset 2 :inverted-from 0)]
                     :heads [{:x 0 :y 0 :z 0
                              :channels [(assoc (channels/color 3 :red) :inverted-from 0)]}]}]
    ;; Install the old layout without admission checks to exercise blackout on an existing conflict.
    (swap! (:fixtures *show*) assoc :old-fixture (channels/patch-fixture old-fixture 1 1 (constantly 0)))
    (is (= [[1 512 {1 255, 4 255} nil]] (capture-blackout show/blackout-show)))))

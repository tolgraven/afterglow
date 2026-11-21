(ns afterglow.channels-test
  (:require [clojure.test :refer :all]
            [afterglow.channels :as channels]))

(deftest patching-preserves-definitions-and-addresses-fixture-heads
  (let [definition {:name "Two pixels"
                    :channels [(channels/fine-channel :pan 1 :fine-offset 2)]
                    :heads [{:name "Pixel" :channels [(channels/color 3 :red)
                                                     (channels/color 4 :green)
                                                     (channels/color 5 :blue)]}]}
        patched (channels/patch-fixture definition 7 100 (constantly 42))
        pan (first (:channels patched))
        head (first (:heads patched))]
    (is (= {:offset 1 :fine-offset 2 :address 100 :fine-address 101
            :index 99 :fine-index 100 :universe 7}
           (select-keys pan [:offset :fine-offset :address :fine-address
                             :index :fine-index :universe])))
    (is (= [102 103 104] (mapv :address (:channels head))))
    (is (= [101 102 103] (mapv :index (:channels head))))
    (is (= [7 7 7] (mapv :universe (:channels head))))
    (is (= 42 (:id head)))
    (is (= definition (:fixture head)))
    (is (every? #(= "Pixel" (get-in % [:head :name])) (:channels head)))
    (is (= #{100 101 102 103 104} (set (channels/all-addresses [patched]))))
    (is (not-any? :address (:channels definition)))
    (is (nil? (get-in definition [:heads 0 :id])))))

(deftest function-ranges-cover-the-declared-boundaries
  (let [functions (:functions (channels/functions :strobe 8
                                                 0 nil
                                                 10 "Open"
                                                 11 :strobe
                                                 200 {:type :random-strobe
                                                      :label "Random"}))]
    (is (= [[0 9 :fixed :no-function]
            [10 10 :fixed :open]
            [11 199 :variable :strobe]
            [200 255 :variable :random-strobe]]
           (mapv (juxt :start :end :range :type) functions)))
    (is (= "Random" (:label (last functions))))))

(deftest malformed-function-order-and-channel-offsets-are-rejected
  (is (thrown? IllegalArgumentException
               (channels/functions :mode 1 0 :first 0 :second)))
  (is (thrown? IllegalArgumentException
               (channels/functions :mode 1 0 :first 257 :second)))
  (doseq [offset [0 513 1.5]]
    (is (thrown? AssertionError (channels/fine-channel :pan offset)))))

(deftest rgb-selection-includes-pixels-and-optionally-color-wheels
  (let [rgb {:name "RGB" :channels (mapv channels/color [1 2 3] [:red :green :blue])}
        partial {:name "RG" :channels (mapv channels/color [1 2] [:red :green])}
        wheel {:name "Wheel" :color-wheel-hue-map {120 :green}}
        fixture {:name "Fixture" :heads [rgb partial wheel]}]
    (is (= ["RGB"] (mapv :name (channels/find-rgb-heads [fixture]))))
    (is (= ["RGB" "Wheel"] (mapv :name (channels/find-rgb-heads [fixture] true))))
    (is (= ["Fixture" "RGB" "RG" "Wheel"]
           (mapv :name (channels/expand-heads [fixture]))))))

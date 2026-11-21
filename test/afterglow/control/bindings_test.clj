(ns afterglow.control.bindings-test
  (:require [clojure.test :refer [deftest is]]
            [afterglow.control.bindings :as bindings]))

(deftest scale-clamp-and-quantize-compose
  (is (= 0.5 (bindings/scale 63.5 [0 127] [0.0 1.0])))
  (is (= 1.0 (bindings/scale 999 [0 127] [0.0 1.0])))
  (is (= 0.0 (bindings/scale 127 [0 127] [1.0 0.0])))
  (is (= 0.5 (bindings/quantize 0.53 0.1 0.0)))
  (is (thrown? clojure.lang.ExceptionInfo (bindings/scale 1 [1 1] [0 1])))
  (is (thrown? clojure.lang.ExceptionInfo (bindings/quantize 1 0 0))))

(deftest input-matching-and-relative-accumulation
  (let [binding {:event {:type :control-change :controller 2}
                 :command {:op :param/set :instance-id "a" :param :level}
                 :mode :relative :output-range [0 1] :step 0.1 :target-value 0.5}
        envelope {:command-id "encoder-1" :show-id :main :epoch 0 :source :midi}
        result (bindings/apply-input {} {:type :control-change :controller 2 :value 2} binding envelope)]
    (is (= 0.7 (get-in result [:state :value])))
    (is (= :param/set (get-in result [:commands 0 :op])))
    (is (= "encoder-1" (get-in result [:commands 0 :command-id])))
    (is (= 1 (get-in (bindings/apply-input (:state result) {:type :control-change :controller 2 :value 20} binding envelope)
                    [:state :value])))
    (is (= {:state {} :commands []}
           (bindings/apply-input {} {:type :control-change :controller 3 :value 2} binding envelope)))))

(deftest soft-takeover-waits-until-input-crosses-authoritative-value
  (let [binding {:event {:type :slider} :command {:op :master/set}
                 :pickup? true :target-value 0.6 :output-range [0 1]}
        first-result (bindings/apply-input {} {:type :slider :value 0.1} binding {})
        next-result (bindings/apply-input (:state first-result) {:type :slider :value 0.8} binding {})]
    (is (= [] (:commands first-result)))
    (is (= 0.8 (get-in next-result [:commands 0 :value])))
    (is (= false (:picked-up? (bindings/reset-pickup (:state next-result) 0.3))))))

(deftest release-before-ack-is-held-until-exact-instance-is-known
  (let [begin (bindings/begin-hold {} :red {:command-id "press-a" :time-ms 0})
        release (bindings/end-hold (:state begin) "press-a" {:command-id "release-a" :time-ms 10})
        acknowledged (bindings/acknowledge-hold (:state release) "press-a" {:status :accepted :instance-id "0:3"})]
    (is (= :held (get-in begin [:commands 0 :launch :mode])))
    (is (= [] (:commands release)))
    (is (= [{:command-id "release-a" :time-ms 10 :op :instance/end :instance-id "0:3"}]
           (:commands acknowledged)))
    (is (= [] (:commands (bindings/acknowledge-hold (:state acknowledged) "press-a"
                           {:status :accepted :instance-id "0:3"}))))))

(deftest simultaneous-holds-release-independently-and-rejections-clean-up
  (let [a (bindings/begin-hold {} :red {:command-id "a"})
        b (bindings/begin-hold (:state a) :red {:command-id "b"})
        ack (bindings/acknowledge-hold (:state b) "a" {:status :accepted :instance-id "0:1"})
        ended (bindings/end-hold (:state ack) "a" {:command-id "end-a"})
        rejected (bindings/acknowledge-hold (:state ended) "b" {:status :rejected})]
    (is (= "0:1" (get-in ended [:commands 0 :instance-id])))
    (is (contains? (get-in ended [:state :gestures]) "b"))
    (is (= {} (get-in rejected [:state :gestures])))
    (is (= [] (:commands rejected)))))

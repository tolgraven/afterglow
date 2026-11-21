(ns afterglow.control.codecs.push-3-test
  (:require [clojure.test :refer [deftest is]]
            [afterglow.control.codecs.push-3 :as push]))

(def captured
  ;; Synthetic captures deliberately use addresses unrelated to the Push 2 map.
  {:pads {[0 0] {:channel 3 :note 12} [1 0] {:channel 3 :note 13}}
   :encoder-touches {:level {:channel 2 :note 9}}
   :encoders {:level {:channel 2 :controller 19}}
   :buttons {:blackout {:channel 4 :controller 22}}
   :touch-strip {:channel 5} :mono-pressure {:channel 3}})

(deftest captured-addresses-and-message-families-stay-distinct
  (let [layout (push/compile-layout captured) decode #(push/decode layout %)]
    (is (= {:type :pad :control-id [0 0] :pressed? true :gesture-key [3 12]}
           (select-keys (decode [0x93 12 100]) [:type :control-id :pressed? :gesture-key])))
    (is (false? (:pressed? (decode [0x93 12 0]))))
    (is (false? (:pressed? (decode [0x83 12 15]))))
    (is (= :encoder-touch (:type (decode [0x92 9 127]))))
    (is (= -1 (:delta (decode [0xb2 19 127]))))
    (is (= :button (:type (decode [0xb4 22 127]))))
    (is (= :poly-pressure (:type (decode [0xa3 12 99]))))
    (is (= :mono-pressure (:type (decode [0xd3 99]))))
    (is (= 0 (:signed-value (decode [0xe5 0 64]))))
    (is (every? nil? (map decode [[0x90 12 127] [0x93 99 127] [0xa2 9 50]
                                  [0xd4 99] [0xe6 0 64] [0xf8] [0xf0 0 33 29 0 1 9 0xf7]])))))

(deftest capture-is-explicit-pure-and-validates-ambiguity
  (let [learned (-> {} (push/capture {:kind :pad :id [7 7] :bytes [0x96 31 127]})
                    (push/capture {:kind :encoder :id :level :bytes [0xb4 27 1]}))]
    (is (= {:pads {[7 7] {:channel 6 :note 31}}
            :encoders {:level {:channel 4 :controller 27}}} learned))
    (is (thrown? clojure.lang.ExceptionInfo (push/capture learned {:kind :pad :id [0 0] :bytes [0x96 31 0]})))
    (is (thrown? clojure.lang.ExceptionInfo (push/capture learned {:kind :encoder-touch :id :touch :bytes [0x96 31 127]}))))
  (doseq [layout [{:pads {[8 0] {:channel 0 :note 1}}}
                  {:encoders {:a {:channel 16 :controller 1}}}
                  {:encoders {:a {:channel 0 :controller 1 :extra 1}}}
                  {:push-2-defaults true} {:mono-pressure {:channel -1}}]]
    (is (thrown? clojure.lang.ExceptionInfo (push/compile-layout layout)))))

(deftest relative-encoders-use-twos-complement
  (is (= [0 1 63 -64 -1] (mapv push/signed-encoder [0 1 63 64 127])))
  (is (thrown? clojure.lang.ExceptionInfo (push/signed-encoder 128))))

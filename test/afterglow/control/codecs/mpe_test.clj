(ns afterglow.control.codecs.mpe-test
  (:require [clojure.test :refer [deftest is]]
            [afterglow.control.codecs.mpe :as mpe]))

(def zone (mpe/compile-zone {:manager-channel 0 :member-channels [1 2 3]}))

(defn step [state bytes] (mpe/advance zone state bytes))

(deftest per-note-channel-identities-and-before-note-expression
  (let [a (step (mpe/initial-state) [0xb1 74 127])
        b (step (:state a) [0x91 60 127])
        c (step (:state b) [0x92 60 64])
        pressure (step (:state c) [0xd1 100])
        glide (step (:state pressure) [0xe2 0 0])]
    (is (= [] (:events a)))
    (is (= 1.0 (get-in b [:events 0 :axes :slide])))
    (is (= 0.5 (get-in c [:events 0 :axes :slide])))
    (is (= [1 60 1] (get-in pressure [:events 0 :voice-id])))
    (is (= [2 60 2] (get-in glide [:events 0 :voice-id])))
    (is (= -1.0 (get-in glide [:events 0 :value])))
    (let [ended (step (:state glide) [0x81 60 80])
          another (step (:state ended) [0x91 61 127])]
      (is (= (/ 80 127.0) (get-in ended [:events 0 :axes :lift])))
      (is (= 0.5 (get-in another [:events 0 :axes :slide])))
      (is (= [2 60 2] (get-in another [:state :voices [2 60] :voice-id]))))))

(deftest rotation-retrigger-ambiguity-and-manager-do-not-collapse-notes
  (let [a (step (mpe/initial-state) [0x91 60 127])
        b (step (:state a) [0x91 61 127])
        ambiguous (step (:state b) [0xd1 100])
        manager (step (:state b) [0xe0 127 127])
        reattack (step (:state a) [0x91 60 99])]
    (is (= 2 (count (get-in b [:state :voices]))))
    (is (= [] (:events ambiguous)))
    (is (= :ambiguous-member-channel (get-in ambiguous [:diagnostics 0 :code])))
    (is (= [:zone-axis] (mapv :type (:events manager))))
    (is (= [:note-off :note-on] (mapv :type (:events reattack))))
    (is (= [[1 60 1] [1 60 2]] (mapv :voice-id (:events reattack))))
    (is (= [] (:events (step (:state a) [0x82 60 0]))))
    (is (= [] (:events (step (:state a) [0x91 90 0]))))
    (is (= [:note-off :note-off] (mapv :type (:events (step (:state b) [0xb1 123 0])))))))

(deftest explicit-contiguous-zones-and-normalized-bend
  (is (= #{13 14} (:member-channels (mpe/compile-zone {:manager-channel 15 :member-channels [13 14]}))))
  (doseq [invalid [{:manager-channel 0 :member-channels []} {:manager-channel 1 :member-channels [2]}
                   {:manager-channel 0 :member-channels [1 3]} {:manager-channel 0 :member-channels [1 1]}]]
    (is (thrown? clojure.lang.ExceptionInfo (mpe/compile-zone invalid))))
  (let [state (:state (step (mpe/initial-state) [0x91 60 127]))]
    (is (= [0.0 1.0 -1.0] (mapv #(get-in (step state %) [:events 0 :value]) [[0xe1 0 64] [0xe1 127 127] [0xe1 0 0]])))
    (is (= [] (:events (step state [0xf8]))))))

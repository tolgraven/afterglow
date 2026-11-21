(ns afterglow.control.codecs.midi-test
  (:require [clojure.test :refer [deftest is testing]]
            [afterglow.control.codecs.midi :as midi]))

(deftest note-and-pressure-messages
  (is (= {:type :note-on :channel 2 :note 60 :velocity 127 :value 1.0}
         (midi/decode [0x92 60 127])))
  (is (= {:type :note-off :channel 2 :note 60 :velocity 0 :value 0.0}
         (midi/decode [0x92 60 0])))
  (is (= {:type :note-off :channel 2 :note 60 :velocity 64 :value (/ 64 127.0)}
         (midi/decode [0x82 60 64])))
  (is (= {:type :poly-pressure :channel 15 :note 99 :pressure 80 :value (/ 80 127.0)}
         (midi/decode [0xaf 99 80])))
  (is (= {:type :channel-pressure :channel 0 :pressure 127 :value 1.0}
         (midi/decode [0xd0 127]))))

(deftest cc-and-pitch-bend-byte-order
  (is (= {:type :control-change :channel 7 :controller 10 :raw-value 64 :value (/ 64 127.0)}
         (midi/decode [0xb7 10 64])))
  (doseq [[bytes raw signed] [[[0xe0 0 0] 0 -8192]
                             [[0xe0 0 64] 8192 0]
                             [[0xe0 1 64] 8193 1]
                             [[0xe0 127 127] 16383 8191]]]
    (is (= {:type :pitch-bend :channel 0 :raw-value raw :signed-value signed :value (/ raw 16383.0)}
           (midi/decode bytes)))))

(deftest all-channels-and-data-boundaries-round-trip
  (doseq [channel (range 16)
          value [0 1 63 64 126 127]
          message [[(+ 0x80 channel) 60 value]
                   [(+ 0x90 channel) 60 (max 1 value)]
                   [(+ 0xa0 channel) 60 value]
                   [(+ 0xb0 channel) 10 value]
                   [(+ 0xc0 channel) value]
                   [(+ 0xd0 channel) value]
                   [(+ 0xe0 channel) value 64]]]
    (is (= message (midi/encode (midi/decode message))))))

(deftest malformed-messages-are-rejected
  (doseq [message [[] [60 1 2] [0x90 60] [0x90 60 1 0]
                   [0xd0 1 2] [0x90 -1 1] [0x90 60 128]
                   [0x90 60 0.5] [0xf0 1 2] [0x100 1 2]]]
    (is (thrown? clojure.lang.ExceptionInfo (midi/decode message))))
  (doseq [event [{:type :note-on :channel 16 :note 60 :velocity 1}
                 {:type :pitch-bend :channel 0 :raw-value 16384}
                 {:type :control-change :channel 0 :controller 1 :value 0.5}
                 {:type :unknown :channel 0}]]
    (is (thrown? clojure.lang.ExceptionInfo (midi/encode event)))))

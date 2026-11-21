(ns afterglow.control.codecs.x-touch-test
  (:require [clojure.test :refer :all]
            [afterglow.control.codecs.x-touch :as codec]))

;; Fixed source-derived protocol examples, not recordings from physical gear.
;; MainDisplay.py/consts.py/ChannelStrip.py at codec/reference revision.
(deftest protocol-reference-examples
  (is (= [240 0 0 102 20 114 0 1 2 3 4 5 6 7 247] (codec/colors false [0 1 2 3 4 5 6 7])))
  (is (= [240 0 0 102 21 114 7 7 7 7 7 7 7 7 247] (codec/colors true [7 7 7 7 7 7 7 7])))
  (is (= [240 0 0 102 20 18 0 69 109 98 101 114 247] (codec/text false 0 0 "Ember")))
  (is (= [240 0 0 102 21 18 63 88 247] (codec/text true 1 7 "X")))
  (is (= [240 0 0 102 20 18 55 63 247] (codec/text false 0 55 "灯")))
  (is (= [224 0 0] (codec/fader 0 0)))
  (is (= [232 127 127] (codec/fader 8 1)))
  (is (= [226 0 64] (codec/fader 2 0.5)))
  (is (= [176 51 27] (codec/encoder-ring 3 11 :boost-cut)))
  (is (= [144 24 127] (codec/button-led 24 :on)))
  (is (= [144 24 1] (codec/button-led 24 :blink)))
  (is (= [144 24 0] (codec/button-led 24 :off))))

(deftest decoded-input-preserves-resolution-direction-and-release
  (is (= {:type :fader :strip 7 :raw-value 16383 :value 1.0} (codec/decode [231 127 127])))
  (is (= {:type :touch :strip 8 :pressed? true} (codec/decode [144 112 127])))
  (is (= {:type :touch :strip 0 :pressed? false} (codec/decode [128 104 127])))
  (is (= {:type :button :note 24 :pressed? false} (codec/decode [144 24 0])))
  (is (= {:type :encoder :strip 0 :delta -3} (codec/decode [176 16 67])))
  (is (= {:type :encoder :strip 7 :delta 4} (codec/decode [176 23 4])))
  (is (= {:type :jog :delta -1} (codec/decode [176 60 65])))
  (is (nil? (codec/decode [145 24 127])) "buttons belong to MCU channel zero")
  (is (nil? (codec/decode [240 0 0 102 20 247])))
  (doseq [raw [0 1 127 128 8191 8192 16382 16383] strip [0 4 8]]
    (let [message [(+ 224 strip) (bit-and raw 127) (bit-shift-right raw 7)]
          event (codec/decode message)]
      (is (= raw (:raw-value event)))
      (is (= message (codec/fader strip (:value event)))))))

(deftest malformed-messages-never-produce-partial-protocol-output
  (doseq [call [#(codec/decode [224 0]) #(codec/decode [176 16 128]) #(codec/decode [144 -1 1])
                #(codec/fader 9 0) #(codec/fader 0 Double/NaN) #(codec/fader 0 1.1)
                #(codec/encoder-ring 8 1) #(codec/encoder-ring 0 12) #(codec/encoder-ring 0 1 :unknown)
                #(codec/colors false [1 2]) #(codec/colors true [0 1 2 3 4 5 6 8])
                #(codec/text false 1 55 "AB") #(codec/text true 2 0 "A") #(codec/button-led 1 :heartbeat)]]
    (is (thrown? clojure.lang.ExceptionInfo (call)))))

(deftest native-palette-and-explicit-temporal-research-helper
  (doseq [[index rgb] (map-indexed vector codec/palette-rgb)] (is (= index (codec/palette-index rgb))))
  (is (not= 0 (codec/palette-index [0.01 0 0])) "active dark red does not silently become black")
  (let [frames (mapv #(codec/temporal-color-frame [0.5 0.25 0] % 4) (range 4))]
    (is (= [3 1 0 0] frames))
    (is (= [0.5 0.25 0.0] (mapv #(/ % 4.0) (apply mapv + (map codec/palette-rgb frames))))))
  (is (thrown? clojure.lang.ExceptionInfo (codec/temporal-color-frame [1 0 0] 0 0))))

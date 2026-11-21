(ns afterglow.control.codecs.push-2-test
  (:require [clojure.test :refer [deftest is]]
            [afterglow.control.codecs.push-2 :as push]))

(deftest pad-grid-and-encoder-sign-match-existing-adapter
  (is (= [36 43 92 99] (mapv (fn [[x y]] (push/pad-note x y)) [[0 0] [7 0] [0 7] [7 7]])))
  (doseq [x (range 8) y (range 8)]
    (is (= [x y] (push/pad-coordinates (push/pad-note x y)))))
  (is (nil? (push/pad-coordinates 35)))
  (is (nil? (push/pad-coordinates 100)))
  (is (= [0 1 63 -64 -1] (mapv push/signed-encoder [0 1 63 64 127]))))

(deftest palette-encoding-preserves-low-high-order-and-white
  (is (= [0xf0 0 0x21 0x1d 2 1 4 127 0xf7] (push/palette-request 2 127)))
  (is (= [0xf0 0 0x21 0x1d 2 1 3 36 127 1 0 1 127 0 1 1 0xf7]
         (push/palette-write 2 36 [255 128 127 129]))))

(deftest palette-replies-round-trip-components
  (doseq [value (range 256)]
    (let [write (push/palette-write 3 42 [value (- 255 value) 128 129])
          reply (assoc write 6 4)]
      (is (= {:index 42 :rgbw [value (- 255 value) 128 129]}
             (push/palette-reply 3 reply)))))
  (is (nil? (push/palette-reply 4 (assoc (push/palette-write 3 42 [1 2 3 4]) 6 4))))
  (is (nil? (push/palette-reply 3 (push/palette-write 3 42 [1 2 3 4])))))

(deftest pad-led-plans-match-existing-adapter-protocol
  (is (= [[0x80 36 0]] (push/pad-led-messages 2 0 0 [0 0 0] 42)))
  (is (= [(push/palette-write 2 99 [255 10 0 42]) [0x90 99 99]]
         (push/pad-led-messages 2 7 7 [255 10 0] 42)))
  (is (false? (:hardware-verified? push/capabilities))))

(deftest malformed-push-values-fail-before-message-generation
  (doseq [f [#(push/pad-note -1 0) #(push/pad-note 0 8)
             #(push/signed-encoder 128) #(push/palette-request 128 0)
             #(push/palette-write 0 128 [1 2 3 4])
             #(push/palette-write 0 0 [1 2 3])
             #(push/palette-write 0 0 [1 2 3 256])
             #(push/pad-led-messages 0 0 0 [1 2] 0)
             #(push/sysex 0 [128])
             #(push/palette-reply 0 [0xf0 0 0x21 0x1d 0 1 4 1 0xf7])
             #(push/palette-reply 0 (assoc (assoc (push/palette-write 0 0 [1 2 3 4]) 6 4) 9 2))]]
    (is (thrown? clojure.lang.ExceptionInfo (f)))))

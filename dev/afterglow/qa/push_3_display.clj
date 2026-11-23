(ns afterglow.qa.push-3-display
  "Replay real 960×160 browser capture PNGs through the Push 3 image sink.
  Decode its recorded transfers with an independent reference, checking every pixel."
  (:require [clojure.java.io :as io]
            [afterglow.control.devices.push-3.display :as display]
            [afterglow.control.devices.push-3.qualification :as qualification]
            [afterglow.control.devices.push-3.screen :as screen])
  (:import [java.awt.image BufferedImage]
           [javax.imageio ImageIO]))

(defn- decode [^bytes payload ^BufferedImage expected]
  (let [result (BufferedImage. 960 160 BufferedImage/TYPE_INT_RGB)
        source (.getRGB expected 0 0 960 160 nil 0 960)
        rgb (int-array (* 960 160))]
    (dotimes [y 160]
      (dotimes [x 960]
        (let [i (+ (* y 960) x) offset (+ (* y 2048) (* 2 x))
              word (bit-xor (bit-and 255 (aget payload offset))
                            (bit-shift-left (bit-and 255 (aget payload (inc offset))) 8)
                            (if (zero? (bit-and x 1)) 0xf3e7 0xffe7))
              r (bit-and 31 word) g (bit-and 63 (bit-shift-right word 5)) b (bit-shift-right word 11)
              expected (aget source i)
              pixel (bit-or (bit-shift-left r 19) (bit-shift-left g 10) (bit-shift-left b 3))]
          (when (not= pixel (bit-and expected 0xf8fcf8))
            (throw (ex-info "Pixel mismatch" {:x x :y y :expected expected :actual pixel})))
          (aset-int rgb i pixel))))
    (.setRGB result 0 0 960 160 rgb 0 960)
    result))

(defn- encode-times [image]
  (let [buffers (screen/buffers)]
    (dotimes [_ 40] (screen/encode! buffers image))
    (let [samples (sort (repeatedly 120 #(let [start (System/nanoTime)]
                                          (screen/encode! buffers image)
                                          (/ (- (System/nanoTime) start) 1e6))))]
      {:measurements 120 :p50-ms (nth samples 59) :p95-ms (nth samples 113)})))

(defn -main [input-directory output-directory]
  (let [input (io/file input-directory) output (io/file output-directory)
        files (sort (filter #(re-matches #"[0-9]{2}\.png" (.getName ^java.io.File %)) (.listFiles input)))
        _ (when (empty? files) (throw (ex-info "Supply numbered 960×160 capture PNGs" {})))
        _ (.mkdirs output)
        transfer (atom nil) refresh (atom nil)
        sink (display/sink {:backend {:open! (constantly :replay)
                                      :write! (fn [_ ^bytes bytes]
                                                (if (= 16 (alength bytes))
                                                  (when-not (java.util.Arrays/equals ^bytes (screen/header) bytes)
                                                    (throw (ex-info "Bad header" {})))
                                                  (reset! transfer bytes)))
                                      :close! (fn [_])}
                            :schedule! (fn [tick] (reset! refresh tick) (fn []))})
        handle ((:open! sink))]
    (try
      (doseq [[name read] (concat [["chart.png" qualification/chart]]
                                  (map (fn [file] [(.getName ^java.io.File file) #(ImageIO/read ^java.io.File file)]) files))]
        (let [image (read)]
          ((:render! sink) handle image)
          (@refresh)
          (ImageIO/write (decode @transfer image) "png" (io/file output name))))
      (prn {:replayed (count files) :chart true :pixels-verified (* 960 160 (inc (count files)))
            :usb-header 16 :usb-payload 327680 :encoding (encode-times (ImageIO/read ^java.io.File (first files)))})
      (finally ((:close! sink) handle)))))

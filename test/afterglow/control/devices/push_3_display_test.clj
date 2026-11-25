(ns afterglow.control.devices.push-3-display-test
  (:require [clojure.java.io :as io]
            [clojure.java.shell :as shell]
            [clojure.test :refer [deftest is testing]]
            [afterglow.control.devices.push-3.display :as display]
            [afterglow.control.devices.push-3.screen :as screen]
            [afterglow.control.devices.push-3.usb :as usb])
  (:import [com.sun.jna Function NativeLibrary]
           [java.awt.image BufferedImage]
           [java.nio.file Files]))

(defn- unsigned [xs] (mapv #(bit-and 255 %) xs))

(deftest first-and-last-pixels-and-black-stride-padding
  (let [image (BufferedImage. 960 160 BufferedImage/TYPE_INT_RGB)
        buffers (screen/buffers)]
    (doseq [[x rgb] [[0 0xff0000] [1 0x00ff00] [2 0x0000ff] [959 0xffffff]]]
      (.setRGB image x 0 rgb))
    (.setRGB image 959 159 0x0000ff)
    (let [wire (screen/encode! buffers image)]
      (is (identical? (:wire buffers) wire))
      (is (= 327680 (alength ^bytes wire)))
      (is (= [248 243 7 248 231 11] (unsigned (take 6 wire))))
      (is (= [24 0 231 243 231 255] (unsigned (take 6 (drop 1918 wire)))))
      (is (= [231 7 231 243] (unsigned (take 4 (drop (+ (* 159 2048) 1918) wire)))))
      (is (= (take 128 (cycle [231 243 231 255])) (unsigned (take-last 128 wire)))))
    (is (thrown? Exception (screen/encode! buffers (BufferedImage. 160 960 BufferedImage/TYPE_INT_RGB))))
    (is (= [255 204 170 136] (unsigned (take 4 (screen/header)))))
    (is (= (repeat 12 0) (drop 4 (screen/header))))))

(deftest device-selection-refuses-ambiguous-interfaces
  (let [info {:vendor-id screen/vendor :product-id screen/product}
        display {:interface 0 :alternate 0 :class [255 255 255] :name-index 4
                 :endpoints-count 2 :endpoints [[1 2 512] [129 2 512]]}
        layout {:configuration 1 :interfaces [display]}]
    (is (= display (screen/candidate info 1 layout)))
    (is (nil? (screen/candidate (assoc info :product-id 0x1967) 1 layout)))
    (is (nil? (screen/candidate info 2 layout)))
    (doseq [other [(assoc display :interface 6) (assoc display :alternate 1)
                   (assoc display :endpoints-count 1) (assoc display :endpoints [[1 2 512] [1 2 512]])
                   (assoc display :endpoints [[1 2 64] [129 2 64]])]]
      (is (nil? (screen/candidate info 1 (assoc layout :interfaces [other])))))
    (is (nil? (screen/candidate info 1 (assoc layout :interfaces [display (assoc display :alternate 1)]))))
    (doseq [bytes [[] [9 2 9] [9 2 10 0 0 1 0 0 0 0] [9 2 11 0 0 1 0 0 0 0 4]]]
      (is (thrown? Exception (screen/configuration (byte-array bytes)))))))

(deftest cached-frame-refresh-and-release
  (let [calls (atom []) callback (atom nil) broken? (atom false)
        backend {:open! (fn [_] (swap! calls conj :open) :wire)
                 :write! (fn [_ ^bytes bs]
                           (swap! calls conj (alength bs))
                           (when (and @broken? (= screen/payload-length (alength bs)))
                             (throw (ex-info "USB unplugged" {}))))
                 :close! (fn [_] (swap! calls conj :close))}
        sink (display/sink {:backend backend :schedule! (fn [f] (reset! callback f) #(swap! calls conj :cancel))})
        handle ((:open! sink))
        image (BufferedImage. 960 160 BufferedImage/TYPE_INT_RGB)]
    (@callback)
    (is (= [:open] @calls))
    ((:render! sink) handle image)
    ((:render! sink) handle image)
    (@callback)
    (is (= [:open 16 327680 16 327680] @calls))
    (reset! broken? true)
    (is (thrown? Exception (@callback)))
    (is (thrown? Exception ((:render! sink) handle image)))
    ((:close! sink) handle)
    (@callback)
    (is (= [:open 16 327680 16 327680 16 327680 :cancel :close] @calls))))

(deftest receipts-are-only-for-frames-completing-both-writes
  (let [refresh (atom nil) receipts (atom []) fail? (atom false)
        writes (atom 0)
        sink (display/sink {:backend {:open! (constantly :injected)
                                      :close! (fn [_])
                                      :write! (fn [_ ^bytes bytes]
                                                (swap! writes inc)
                                                (when (and @fail? (= screen/payload-length (alength bytes)))
                                                  (throw (ex-info "Injected short transfer" {}))))}
                            :schedule! #(do (reset! refresh %) (fn []))})
        handle ((:open! sink))
        image (BufferedImage. 960 160 BufferedImage/TYPE_INT_RGB)
        render! (fn [frame] ((:render-with-receipt! sink) handle image
                             #(swap! receipts conj [frame @writes])))]
    (try
      (render! :first)
      (render! :dropped)
      (render! :latest)
      (is (= [[:first 2]] @receipts))
      (@refresh)
      (@refresh)
      (is (= [[:first 2] [:latest 4]] @receipts))
      (render! :failed)
      (reset! fail? true)
      (is (thrown? Exception (@refresh)))
      (is (= [[:first 2] [:latest 4]] @receipts))
      (finally ((:close! sink) handle)))))

(deftest linux-libusb-ffi-replay
  (when (= "Linux" (System/getProperty "os.name"))
    (let [file (.toFile (Files/createTempFile "push3-recording-" ".so"
                                               (make-array java.nio.file.attribute.FileAttribute 0)))
          path (.getAbsolutePath file)
          build (shell/sh "cc" "-shared" "-fPIC" "-o" path "test/native/push3/recording_libusb.c")]
      (try
        (is (zero? (:exit build)) (:err build))
        (with-open [lib (NativeLibrary/getInstance path)]
          (let [^Function reset-fn (.getFunction lib "replay_reset")
                ^Function count-fn (.getFunction lib "replay_count")
                reset-mode! #(.invokeVoid reset-fn (to-array [(int %)]))
                counts #(mapv (fn [i] (.invokeInt count-fn (to-array [(int i)]))) (range 8))
                options {:library path :bus 2 :address 7}]
            (reset-mode! 0)
            (is (= [{:vendor-id 0x2982 :product-id 0x1969 :configurations 1 :bus 2 :address 7}]
                   (usb/locations options)))
            (is (= screen/display-name (get-in (usb/inspect options) [:display :name])))
            (is (= [2 2 1 1 0 0 0 0] (counts)))
            (doseq [mode [1 2 3 4]]
              (reset-mode! mode)
              (is (thrown? Exception (usb/open! options)))
              (is (= [1 1 1 1 0 0 0 0] (counts))))
            (reset-mode! 0)
            (is (thrown? Exception (usb/open! (assoc options :address 5))))
            (is (= [1 1 0 0 0 0 0 0] (counts)))
            (doseq [mode [0 5]]
              (reset-mode! mode)
              (let [handle (usb/open! options)]
                (try
                  (usb/write! handle (screen/header))
                  (if (zero? mode)
                    (usb/write! handle (:wire (screen/buffers)))
                    (is (thrown-with-msg? Exception #"Incomplete" (usb/write! handle (:wire (screen/buffers))))))
                  (finally (usb/close! handle))))
              (is (= [1 1 1 1 1 1 1 1] (counts))))))
        (finally (io/delete-file file true))))))

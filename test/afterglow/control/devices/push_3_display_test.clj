(ns afterglow.control.devices.push-3-display-test
  (:require [clojure.java.io :as io]
            [clojure.java.shell :as shell]
            [clojure.test :refer [deftest is testing]]
            [afterglow.control.devices.push-3.display :as display]
            [afterglow.control.devices.push-3.qualification :as qualification]
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

(deftest refresh-receipt-counts-frames-bytes-and-transfer-times
  (let [refresh (atom nil)
        sink (display/sink {:backend {:open! (constantly {:timing {:context :reused :open-ms 3.0}})
                                      :write! (fn [_ ^bytes bytes]
                                                (when (= screen/payload-length (alength bytes)) (Thread/sleep 2)))
                                      :close! (fn [_])}
                            :schedule! #(do (reset! refresh %) (fn []))})
        handle ((:open! sink))
        image (BufferedImage. 960 160 BufferedImage/TYPE_INT_RGB)]
    (is (= 0 (:frames (display/refresh-receipt handle))))
    ((:render! sink) handle image)
    (dotimes [_ 3] (@refresh))
    ((:close! sink) handle)
    (@refresh)
    (let [receipt (display/refresh-receipt handle)]
      (is (= 4 (:frames receipt)))
      (is (= (* 4 (+ 16 screen/payload-length)) (:bytes receipt)))
      (is (nil? (:target-hz receipt)) "an injected schedule owns its cadence")
      (is (= {:context :reused :open-ms 3.0} (:usb receipt)))
      (is (= 4 (get-in receipt [:payload-transfer :samples])))
      (is (<= 2.0 (get-in receipt [:payload-transfer :min-ms])))
      (is (= 3 (get-in receipt [:interval :samples])))
      (is (pos? (:frames-per-second receipt)))
      (is (number? (:open-ms receipt)))
      (is (false? (:failed? receipt))))))

(deftest default-refresh-runs-on-deadlines-despite-slow-transfers
  ;; A 15 ms payload transfer at 40 Hz (25 ms period). Waiting a fixed delay
  ;; after each transfer, as the sink used to, gives intervals of 40 ms or more.
  (let [frames (atom []) done (promise)
        sink (display/sink {:refresh-hz 40
                            :backend {:open! (constantly :replay) :close! (fn [_])
                                      :write! (fn [_ ^bytes bytes]
                                                (when (= screen/payload-length (alength bytes))
                                                  (Thread/sleep 15)
                                                  (when (= 25 (count (swap! frames conj (System/nanoTime))))
                                                    (deliver done true))))}})
        handle ((:open! sink))]
    (try
      ((:render! sink) handle (BufferedImage. 960 160 BufferedImage/TYPE_INT_RGB))
      (is (true? (deref done 5000 false)))
      (finally ((:close! sink) handle)))
    (let [receipt (display/refresh-receipt handle)]
      (is (= 40 (:target-hz receipt)))
      ;; Relative to measured transfers, so a loaded machine cannot fake a pass:
      ;; a fixed delay cannot start frames less than 25 ms + transfer apart.
      (is (< (get-in receipt [:interval :median-ms])
             (+ 20.0 (get-in receipt [:payload-transfer :median-ms])))
          (pr-str receipt)))))

(deftest libusb-ffi-replay-shares-one-context
  (when (#{"Linux" "Mac OS X"} (System/getProperty "os.name"))
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
            (try
              (reset-mode! 0)
              (is (= [{:vendor-id 0x2982 :product-id 0x1969 :configurations 1 :bus 2 :address 7}]
                     (usb/locations options)))
              (is (= screen/display-name (get-in (usb/inspect options) [:display :name])))
              (testing "one libusb_init serves every later call and nothing exits it"
                (is (= [1 0 1 1 0 0 0 0] (counts)))
                (is (= {:library path :reused? true} (dissoc (usb/prepare! options) :init-ms))))
              (doseq [mode [1 2 3 4]]
                (reset-mode! mode)
                (is (thrown? Exception (usb/open! options)))
                (is (= [0 0 1 1 0 0 0 0] (counts))))
              (reset-mode! 0)
              (is (thrown? Exception (usb/open! (assoc options :address 5))))
              (is (= [0 0 0 0 0 0 0 0] (counts)))
              (doseq [mode [0 5]]
                (reset-mode! mode)
                (let [handle (usb/open! options)]
                  (try
                    (is (= :reused (get-in handle [:timing :context])))
                    (is (= 0.0 (get-in handle [:timing :init-ms])))
                    (is (every? #(number? (get-in handle [:timing %])) [:context-init-ms :open-ms :total-ms]))
                    (usb/write! handle (screen/header))
                    (if (zero? mode)
                      (usb/write! handle (:wire (screen/buffers)))
                      (is (thrown-with-msg? Exception #"Incomplete" (usb/write! handle (:wire (screen/buffers))))))
                    (finally (usb/close! handle))))
                (is (= [0 0 1 1 1 1 1 1] (counts))))
              (reset-mode! 0)
              (is (= 1 (usb/release-contexts!)))
              (is (= [0 1 0 0 0 0 0 0] (counts)))
              (testing "after release the next caller creates and times a new context"
                (reset-mode! 0)
                (let [handle (usb/open! options)]
                  (try (is (= :created (get-in handle [:timing :context])))
                       (is (= (get-in handle [:timing :init-ms]) (get-in handle [:timing :context-init-ms])))
                       (finally (usb/close! handle))))
                (is (= [1 0 1 1 1 1 0 0] (counts))))
              (testing "the qualification CLI's timing and show-chart receipts"
                (let [timing (qualification/timing options)]
                  (is (true? (get-in timing [:context :reused?])))
                  (is (= 1 (count (:locations timing))))
                  (is (= 2 (count (:inspect-ms timing)))))
                (reset-mode! 0)
                (let [receipt (qualification/observe! options 1)]
                  (is (= 30 (:target-hz receipt)))
                  (is (= :reused (get-in receipt [:usb :context])))
                  (is (= (:frames receipt) (nth (counts) 6) (nth (counts) 7)))
                  (is (< 20 (:frames receipt) 40) (pr-str receipt))))
              (testing "release refuses while a handle is open, so no handle outlives its context"
                (reset-mode! 0)
                (let [handle (usb/open! options)]
                  (try (is (thrown-with-msg? Exception #"Close every" (usb/release-contexts!)))
                       (is (zero? (nth (counts) 1)) "libusb_exit was not called under a live handle")
                       (finally (usb/close! handle)))
                  (usb/close! handle)
                  (is (= 1 (nth (counts) 3)) "a second close! does not close the device again"))
                (is (= 1 (usb/release-contexts!)))
                (is (= 1 (nth (counts) 1))))
              (testing "concurrent first callers share one scan; background preparation never throws"
                (reset-mode! 0)
                (let [pending (doall (repeatedly 4 #(usb/prepare-in-background! options)))
                      results (mapv #(deref % 5000 ::timeout) pending)]
                  (is (= 1 (first (counts))))
                  (is (= [false true true true] (sort (map :reused? results))) (pr-str results)))
                (let [missing @(usb/prepare-in-background! {:library "/nonexistent/push3-libusb.dylib"})]
                  (is (true? (:failed? missing)))
                  (is (string? (:error missing)))))
              (finally (usb/release-contexts!)))))
        (finally (io/delete-file file true))))))

(ns afterglow.control.devices.transports-test
  (:require [clojure.test :refer [deftest is]]
            [afterglow.control.devices.push-2 :as push]
            [afterglow.control.devices.transports :as transports]
            [afterglow.control.devices.generic :as generic])
  (:import [java.awt Font]
           [java.awt.image BufferedImage]))

(deftest transports-remain-inert-until-explicit-open
  (is (map? (transports/midi-transport {:input-index 0 :output-index 1})))
  (is (map? (transports/osc-transport {:port 9000})))
  (is (map? (transports/wayang-display)))
  (is (thrown? clojure.lang.ExceptionInfo (transports/midi-transport {:input-index -1 :output-index 0})))
  (is (thrown? clojure.lang.ExceptionInfo (transports/osc-transport {:port 99999}))))

(deftest native-display-lease-is-exclusive-and-cleaned-up
  (let [calls (atom [])
        backend {:open! #(do (swap! calls conj :open) (BufferedImage. 960 160 BufferedImage/TYPE_INT_RGB))
                 :send! #(swap! calls conj :send)
                 :close! #(swap! calls conj :close)}
        a (transports/wayang-display {:backend backend})
        b (transports/wayang-display {:backend backend})
        handle ((:open! a))]
    (try
      (is (thrown? clojure.lang.ExceptionInfo ((:open! b))))
      ((:render! a) handle {:title "Tolglow" :status :ready :parameters [{:name "level" :value 0.5}]})
      (is (= [:open :send] @calls))
      (finally ((:close! a) handle)))
    ((:close! a) handle)
    (is (= [:open :send :close] @calls))
    (let [other ((:open! b))]
      (try
        (is (thrown? clojure.lang.ExceptionInfo ((:render! a) handle {})))
        (finally ((:close! b) other))))))

(deftest push-three-has-no-inferred-push-two-support
  (is (= :unsupported (:display generic/push-3-capabilities)))
  (is (= :unsupported (:standalone generic/push-3-capabilities)))
  (is (false? (:hardware-verified? generic/push-3-capabilities)))
  (is (thrown? clojure.lang.ExceptionInfo (generic/connect-push-3-midi! {}))))

(deftest touch-lock-feedback-reaches-the-physical-display-renderer
  (let [draw (fn [editable?]
               (let [image (BufferedImage. 960 160 BufferedImage/TYPE_INT_RGB)]
                 (transports/render-view! image {:bpm 120 :master 1 :touched-control {:target :tempo :editable? editable?}})
                 (vec (.getRGB image 0 32 960 24 nil 0 960))))]
    (is (not= (draw true) (draw false)))))

(deftest fine-feedback-appears-only-while-held
  (let [image (BufferedImage. 960 160 BufferedImage/TYPE_INT_RGB)
        view {:title "Tolglow" :page :main :status :ready :bpm 120 :master 1
              :blackout? true :touched-control {:target :tempo :editable? false}
              :parameters [{:name "Level" :value 0.5}]}
        pixels (fn [y height] (vec (.getRGB image 0 y 960 height nil 0 960)))
        frame (fn [view]
                (transports/render-view! image view)
                [(pixels 0 32) (pixels 32 24) (pixels 56 104)])
        [header status parameters :as normal] (frame view)
        [fine-header fine-status fine-parameters] (frame (assoc view :fine? true))]
    (is (not= status fine-status))
    (is (= [header parameters] [fine-header fine-parameters]))
    (is (= normal (frame (assoc view :fine? false))))))

(deftest numeric-display-labels-fit-with-their-exponents
  (let [image (BufferedImage. 960 160 BufferedImage/TYPE_INT_RGB)
        graphics (.createGraphics image)]
    (try
      (.setFont graphics (Font. "SansSerif" Font/PLAIN 14))
      (let [metrics (.getFontMetrics graphics)
            available-width 104
            label #(#'transports/parameter-value-label metrics % available-width)
            small (/ 1.0 65535.0)
            large 1.2345678901234567E120
            compact-large "1.23457e120"]
        (is (= "42" (label 42)))
        (is (= "0.51" (label 0.51)))
        (is (= "1/3" (label 1/3)))
        (is (= ":open" (label :open)))
        (is (= "0.123457" (label 0.123456789)))
        (is (= "0.510015" (label (+ 0.51 small))))
        (is (= compact-large
               (#'transports/parameter-value-label metrics large
                                                  (.stringWidth metrics compact-large))))
        (doseq [value [small (- small) large]]
          (let [text (label value)]
            (is (re-find #"[eE][+-]?\d+$" text))
            (is (<= (.stringWidth metrics text) available-width))))
        (doseq [value [small (- small) large]
                :let [text (#'transports/parameter-value-label metrics value 200)]]
          (is (< (Math/abs (- 1.0 (/ (Double/parseDouble text) value))) 1e-5))))
      (finally (.dispose graphics)))))

(deftest native-readouts-distinguish-adjacent-physical-codes
  (let [image (BufferedImage. 960 160 BufferedImage/TYPE_INT_RGB)
        graphics (.createGraphics image)]
    (try
      (.setFont graphics (Font. "SansSerif" Font/PLAIN 14))
      (let [metrics (.getFontMetrics graphics)
            label #(#'transports/parameter-readout metrics % 104)]
        (doseq [[bits code max-code expected] [[8 127 255.0 ["0.498" "0.502"]]
                                               [16 32767 65535.0 ["0.49999" "0.50001"]]]
                :let [parameter {:schema {:type :number :bounds [0 1] :dmx-bits bits}
                                 :value (/ code max-code)}]]
          (is (= expected [(label parameter) (label (assoc parameter :effective-value (/ (inc code) max-code)))])))
        (is (= "-0.12…0.23" (label {:schema {:type :range :bounds [-360 360] :dmx-bits 16}
                                   :value [-0.123 0.234]})))
        (is (= "-0.5 · 0.5" (label {:schema {:type :vector :bounds [-0.5 0.5] :dmx-bits 8}
                                    :value [-0.5 0.5]})))
        (is (= "-0.00002" (label {:schema {:type :number :bounds [-0.5 0.5] :dmx-bits 16}
                                  :value -0.0000153})))
        (is (= "1.0E-10" (label {:schema {:type :number} :value 1e-10})))
        (is (= "0.5" (label {:schema {:type :number :choices true} :value 0.5})))
        (is (= "Pulse" (label {:schema {:type :number :choices [{:value 0.5 :label "Pulse"}]} :value 0.5})))
        (is (= "1" (label {:schema {:type :number :dmx-bits 16 :bounds [Long/MIN_VALUE Long/MAX_VALUE]}
                            :value 1.234})))
        (doseq [[bounds value] [[[(- Double/MAX_VALUE) Double/MAX_VALUE] 1.2e300]
                                [[-1e-300 1e-300] -1.2e-301]
                                [[(- Double/MIN_VALUE) Double/MIN_VALUE] Double/MIN_VALUE]]
                :let [text (label {:schema {:type :number :dmx-bits 16 :bounds bounds} :value value})]]
          (is (= value (Double/parseDouble text)))))
      (finally (.dispose graphics)))))

(deftest native-color-readout-keeps-the-labeled-components-and-physical-precision
  (let [rgb [(/ 32767.0 65535) (/ 32768.0 65535) 1.0]
        schema {:type :color :default rgb :dmx-bits 16}
        instance {:id "0:1" :cue-id :wash :definition {:params {:tint schema}} :params {:tint rgb}}
        view (push/display-view {:selected-instance "0:1" :page-id :main :origin [0 0]}
                                {:instances {"0:1" instance}})
        image (BufferedImage. 960 160 BufferedImage/TYPE_INT_RGB)
        graphics (.createGraphics image)
        pixels (fn [color y height]
                 (transports/render-view! image (assoc-in view [:parameters 0 :effective-value] color))
                 (vec (.getRGB image 0 y 120 height nil 0 120)))]
    (try
      (.setFont graphics (Font. "SansSerif" Font/PLAIN 11))
      (let [metrics (.getFontMetrics graphics)
            readouts #(#'transports/color-readouts metrics (get-in view [:parameters 0 :schema]) %1 %2)]
        (is (= ["R 0.49999" "G 0.50001" "B 1"] (readouts rgb 104)))
        (is (= ["R 0.49999" "G 0.50001" "B 1" "W 0.25"] (readouts (conj rgb 0.25) 104)))
        (let [narrow-width (.stringWidth metrics "R …")
              [red :as narrow] (readouts rgb narrow-width)]
          (is (= "R …" red))
          (is (every? #(<= (.stringWidth metrics ^String %) narrow-width) narrow))))
      (is (not= (pixels nil 101 21) (pixels (assoc rgb 1 0.75) 101 21)))
      (is (not= (pixels nil 122 11) (pixels (conj rgb 0.25) 122 11)))
      (finally (.dispose graphics)))))

(deftest native-waveform-draws-only-current-supplied-samples
  (let [image (BufferedImage. 960 160 BufferedImage/TYPE_INT_RGB)
        parameter {:name "Waveform" :value 0 :preview-status :ready :preview-samples [0 1 0 -1 0]}
        pixels (fn [row options]
                 (transports/render-view! image (assoc options :parameters [row]))
                 (vec (.getRGB image 0 115 120 18 nil 0 120)))
        footer-pixels (fn [row]
                        (transports/render-view! image {:parameters [row] :labels ["Orchid"]})
                        (vec (.getRGB image 0 133 120 27 nil 0 120)))
        empty-pixels (pixels (dissoc parameter :preview-samples) {})]
    (is (not= empty-pixels (pixels parameter {})))
    (is (not= (pixels parameter {}) (pixels (assoc parameter :preview-samples [1 1 0 0 1]) {})))
    (is (= (footer-pixels (dissoc parameter :preview-samples)) (footer-pixels parameter)))
    (is (= empty-pixels (pixels (dissoc parameter :preview-status) {})))
    (is (= empty-pixels (pixels (-> parameter (dissoc :preview-status) (assoc :source-state :active)) {})))
    (is (not= empty-pixels (pixels (assoc parameter :source-state :active) {})))
    (doseq [state [:held :pending :error]]
      (is (= empty-pixels (pixels (assoc parameter :source-state state) {}))))
    (doseq [status [:stale :unavailable]]
      (is (= empty-pixels (pixels (assoc parameter :preview-status status) {}))))
    (is (= empty-pixels (pixels (assoc parameter :preview-samples [0 ##Inf 1]) {})))
    (is (= empty-pixels (pixels parameter {:target-picker {:open? true}})))))

(deftest a-slow-native-driver-never-owns-the-caller-and-retries-reuse-its-scan
  (let [running (promise)
        release (promise)
        calls (atom 0)
        ports [{:index 0 :name "Controller"}]
        enumerate! (fn []
                     (swap! calls inc)
                     (deliver running (.isDaemon (Thread/currentThread)))
                     @release
                     ports)
        list! (#'transports/port-scanner enumerate! 100)
        error-reason (fn [] (try (list!) (catch clojure.lang.ExceptionInfo error (:reason (ex-data error)))))]
    (try
      (is (= :midi/discovery-pending (error-reason)))
      (is (true? (deref running 3000 false)))
      (is (= :midi/discovery-pending (error-reason)))
      (is (= 1 @calls))
      (deliver release true)
      (is (= ports (list!)))
      (is (= 1 @calls))
      (is (= ports (list!)))
      (is (= 2 @calls))
      (finally (deliver release true)))))

(deftest discovery-surfaces-the-original-provider-error-and-can-retry
  (let [attempts (atom 0)
        failure (ex-info "Disconnected MIDI provider" {:device :test})
        list! (#'transports/port-scanner #(if (= 1 (swap! attempts inc)) (throw failure) []) 3000)]
    (is (identical? failure (try (list!) (catch Exception error error))))
    (is (= [] (list!)))))

(deftest reloading-the-device-namespace-keeps-the-process-midi-scan
  (let [owner @#'transports/scan-midi-ports
        release (promise) started (promise)
        slow (fn [] (deliver started true) @release [])
        read-ports (fn [] (try (transports/midi-ports)
                               (catch clojure.lang.ExceptionInfo error (:reason (ex-data error)))))
        task (future (with-redefs-fn {#'transports/enumerate-midi-ports slow} read-ports))]
    (try
      (is (true? (deref started 3000 false)))
      (require 'afterglow.control.devices.transports :reload)
      (is (identical? owner @#'transports/scan-midi-ports))
      (deliver release true)
      (let [result (deref task 3000 ::timeout)]
        (is (= [] (if (= result :midi/discovery-pending) (transports/midi-ports) result))))
      (finally (deliver release true)))))

(deftest deadline-grid-skips-missed-deadlines-instead-of-bursting
  (is (= 110 (transports/next-deadline-ns 100 10 105)))
  (is (= 120 (transports/next-deadline-ns 100 10 110)))
  (is (= 140 (transports/next-deadline-ns 100 10 137)))
  (is (thrown? clojure.lang.ExceptionInfo (transports/deadline-scheduler 0)))
  (is (thrown? clojure.lang.ExceptionInfo (transports/deadline-scheduler 241))))

(deftest deadline-scheduler-stops-on-cancel
  (let [runs (atom 0) started (promise)
        cancel ((transports/deadline-scheduler 200) #(when (= 3 (swap! runs inc)) (deliver started true)))]
    (is (true? (deref started 2000 false)))
    (cancel)
    (let [stopped @runs]
      (Thread/sleep 50)
      (is (<= (- @runs stopped) 1)))))

(deftest deadline-scheduler-never-starts-a-run-after-cancel-returns
  ;; A run re-arming as cancel ran could leave one more run queued a period
  ;; later. Cancel right after a run, when the worker is re-arming, many times.
  (let [period-ns (long (/ 1e9 240))
        runs (vec (for [_ (range 500)]
                    (let [starts (atom []) give-up (+ (System/nanoTime) 2000000000)
                          cancel ((transports/deadline-scheduler 240)
                                  #(swap! starts conj (System/nanoTime)))]
                      ;; Spin, then sweep a few microseconds, so cancel lands while the worker re-arms.
                      (while (and (empty? @starts) (< (System/nanoTime) give-up)))
                      (let [until (+ (System/nanoTime) (rand-int 30000))] (while (< (System/nanoTime) until)))
                      (cancel)
                      [starts (System/nanoTime)])))]
    (Thread/sleep 20)
    ;; A run already in progress may finish; a queued one starts about a period later.
    (is (zero? (count (filter (fn [[starts cancelled]] (some #(> % (+ cancelled (quot period-ns 2))) @starts))
                              runs))))))

(ns afterglow.control.devices.transports-test
  (:require [clojure.test :refer [deftest is]]
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

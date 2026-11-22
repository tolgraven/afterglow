(ns afterglow.control.devices.transports-test
  (:require [clojure.test :refer [deftest is]]
            [afterglow.control.devices.transports :as transports]
            [afterglow.control.devices.generic :as generic])
  (:import [java.awt.image BufferedImage]))

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

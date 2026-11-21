(ns afterglow.control.devices.osc-transport-parity-test
  (:require [clojure.test :refer [deftest is]]
            [afterglow.control.devices.repl :as devices]
            [afterglow.control.devices.transports :as transports]
            [overtone.osc.peer :as peer]))

(deftest bound-ports-round-trip-osc-and-feedback-without-discovery
  (let [before @peer/zero-conf-services*
        receiver (transports/osc-transport {:port-in 0 :bind-host "127.0.0.1"})
        received (promise)
        handle ((:open! receiver) #(deliver received %))]
    (try
      (let [command (promise)
            control (devices/open-osc! {:session-id "desk" :model! (constantly {:show-id :main :epoch 0}) :now-ms! (constantly 0)
                                        :dispatch! #(do (deliver command %) {:status :accepted})
                                        :port-in 0 :bind-host "127.0.0.1"
                                        :address "127.0.0.1" :port-out (:port handle)
                                        :mappings {"/master" {:op :master/set}}})]
        (try
          (is (pos? (devices/osc-port control)))
          (devices/send-osc! control "/level" (float 0.5))
          (is (= {:path "/level" :args [0.5]} (deref received 2000 nil)))
          (let [sender (transports/osc-transport {:port 0 :port-out (devices/osc-port control)})
                outbound ((:open! sender) (fn [_]))]
            (try ((:send! sender) outbound [{:path "/master" :args [(float 0.75)]}])
                 (is (= {:op :master/set :value 0.75}
                        (select-keys (deref command 2000 nil) [:op :value])))
                 (finally ((:close! sender) outbound))))
          (is (= before @peer/zero-conf-services*))
          (finally (devices/close! control)))
        (is (thrown? Exception (devices/send-osc! control "/level" 0))))
      (finally ((:close! receiver) handle)))))

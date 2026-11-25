(ns afterglow.test-runner
  (:require [clojure.test :as test]))

(def pure-tests
  '[afterglow.sync-test afterglow.core-test afterglow.runtime-test afterglow.time-test afterglow.reactive-test
    afterglow.runtime.reuse-test afterglow.runtime.cadence-test afterglow.runtime.engine-test afterglow.runtime.keyframes-test afterglow.runtime.faults-test afterglow.runtime.executor-test afterglow.runtime.replay-test
    afterglow.control.model-test afterglow.control.edit-history-test afterglow.control.clock-test afterglow.control.bindings-test afterglow.control.views-test
    afterglow.control.categories-test afterglow.control.system-test afterglow.control.sensors-test
    afterglow.control.parameter-edit-test afterglow.control.quantization-test afterglow.control.resolution-test afterglow.control.devices.push-2-test
    afterglow.control.codecs.midi-test afterglow.control.codecs.osc-test afterglow.control.codecs.push-2-test
    afterglow.control.codecs.push-3-test afterglow.control.codecs.mpe-test
    afterglow.control.devices.push-3-test afterglow.control.devices.push-3-display-test afterglow.control.devices.mpe-test
    afterglow.control.codecs.x-touch-test afterglow.control.devices.x-touch-test
    afterglow.control.devices.session-test afterglow.control.devices.transports-test
    afterglow.output.artnet-test afterglow.output.ola-test afterglow.output.scheduler-test afterglow.output.timeline-test
    afterglow.rdm.artnet-test afterglow.rdm.transport-test afterglow.spatial-test afterglow.render.easing-test afterglow.spatial-field-test afterglow.spatial.beam-test
    afterglow.render.atmosphere-test afterglow.render.emission-test afterglow.render.hdr-test afterglow.render.atmosphere.calibration-test afterglow.render.compute-test afterglow.render.chain-test afterglow.render.distributed-test afterglow.render.verified-test afterglow.render.photometry-test afterglow.render.frame-test afterglow.render.ir-test afterglow.render.blocks-test afterglow.render.optics-test afterglow.render.edge-tracking-test afterglow.render.layers-test afterglow.render.presentation-test])

(def suites
  {"pure" pure-tests
   "parity" (into pure-tests '[
               afterglow.control.devices.osc-transport-parity-test
               afterglow.output.ola-protocol-parity-test
               afterglow.channels-test afterglow.rhythm-test
               afterglow.controllers.ableton-push-2-test
               afterglow.effects-test afterglow.effects.color-test
               afterglow.effects.pipeline-test afterglow.effects.channel-test
               afterglow.effects.oscillators-test afterglow.effects.movement-test
               afterglow.show-test])})

(defn -main [& [suite & extra]]
  (let [namespaces (get suites (or suite "pure"))]
    (when (or (seq extra) (nil? namespaces))
      (binding [*out* *err*] (println "Usage: bin/test [pure|parity]"))
      (System/exit 2))
    (let [status (try
                   (doseq [namespace namespaces] (require namespace))
                   (let [{:keys [fail error]} (apply test/run-tests namespaces)]
                     (if (zero? (+ fail error)) 0 1))
                   (catch Throwable error
                     (.printStackTrace error)
                     1)
                   (finally (shutdown-agents)))]
      (System/exit status))))

(ns afterglow.control.devices.repl
  "Explicit REPL entry points for real devices. Supply a host model snapshot,
  synchronous command dispatcher and logical clock; importing does no I/O."
  (:require [afterglow.control.devices.session :as session]
            [afterglow.control.devices.push-2 :as push]
            [afterglow.control.devices.push-3 :as push-3]
            [afterglow.control.devices.seaboard :as seaboard]
            [afterglow.control.devices.generic :as generic]
            [afterglow.control.devices.transports :as transports]))

(def ports transports/midi-ports)
(def status session/snapshot)
(def close! session/close!)
(def suspend! session/suspend!)
(def resume! session/resume!)
(def reconnect! session/reconnect!)
(def refresh! session/refresh!)
(def input! session/receive!)

(defn- with-feedback [options]
  (if (contains? options :schedule!) options
      (assoc options :schedule! (transports/scheduler (get options :refresh-ms 40)))))

(defn open-push-2!
  "Open explicit Push 2 MIDI ports and optional native Wayang display.

  Required host options: :session-id, :model!, :dispatch!, :now-ms!.
  Required device options: :input-index/:output-index unless :midi is injected.
  Use ports to discover indices, then supply expected-input-name/output-name to
  detect enumeration changes. Supply actual :device-id and :page-id. Native
  display is opt-in via :native-display? true (requires legacy dependencies).
  Call close! to release feedback scheduling, held cues, ports and display."
  [options]
  (let [options (cond-> (with-feedback options)
                  (not (:midi options)) (assoc :midi (transports/midi-transport options))
                  (and (:native-display? options) (not (:display options)))
                  (assoc :display (transports/wayang-display)))]
    (push/connect! options)))

(defn open-midi! [options]
  (generic/connect-midi! (cond-> options
                          (not (:transport options)) (assoc :transport (transports/midi-transport options)))))

(defn open-osc! [options]
  (generic/connect-osc! (cond-> options
                         (not (:transport options)) (assoc :transport (transports/osc-transport options)))))

(defn open-sensor!
  "Connect any sensor providing an explicit {:open! :send! :close!} transport.
  Normalized input maps go through the same binding and command model."
  [options]
  (when-not (:transport options)
    (throw (ex-info "Sensor adapter requires an explicit transport" {})))
  (generic/connect-sensor! options))

(defn open-push-3-midi!
  "Use only explicit, device-verified generic MIDI mappings. Display/standalone
  and automatic protocol discovery are unsupported; no Push 2 SysEx is sent."
  [options]
  (generic/connect-push-3-midi!
    (cond-> options
      (not (:transport options)) (assoc :transport (transports/midi-transport options)))))

(defn open-push-3!
  "Open the distinct Push 3 User Mode profile, including configured MPE axes.
  Requires the captured layout/expression settings documented by its profile."
  [options]
  (push-3/connect! (cond-> options
                    (not (:transport options)) (assoc :transport (transports/midi-transport options)))))

(defn open-seaboard!
  "Open a Seaboard M with its configured MPE zone and cue/axis mappings."
  [options]
  (seaboard/connect! (cond-> options
                      (not (:transport options)) (assoc :transport (transports/midi-transport options)))))

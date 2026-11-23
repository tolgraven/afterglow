(ns afterglow.control.devices.push-3.display
  "Tethered Push 3 image sink. Cached USB refresh is independent of browser capture."
  (:require [afterglow.control.devices.push-3.screen :as screen]
            [afterglow.control.devices.push-3.usb :as usb]
            [afterglow.control.devices.transports :as transports]))

(defn- stop! [{:keys [state backend wire]}]
  (let [{:keys [open? cancel]} @state]
    (when open?
      (swap! state assoc :open? false)
      (try (when cancel (cancel))
           (finally ((:close! backend) wire))))))

(defn- present! [{:keys [state backend wire header pixels] :as handle}]
  (when (and (:open? @state) (:ready? @state))
    (try ((:write! backend) wire header)
         ((:write! backend) wire (:wire pixels))
         (catch Throwable error
           (swap! state assoc :failure error)
           (stop! handle)
           (throw error)))))

(defn sink
  "Choose :bus and :address from usb/locations, or inject a replay backend.
  One transport owner resends the latest packed frame at 30 Hz. No new browser
  capture or show evaluation is needed for a static screen. A failed or partial
  transfer closes the native handle rather than retrying half a frame."
  [{:keys [backend schedule!] :as options}]
  (let [backend (or backend {:open! usb/open! :write! usb/write! :close! usb/close!})
        schedule! (or schedule! (transports/scheduler 33))]
    {:device :push-3 :input :image
     :open! (fn []
              (let [pixels (screen/buffers) header (screen/header) lock (Object.)
                    state (atom {:open? true})
                    wire ((:open! backend) (dissoc options :backend :schedule!))
                    handle {:pixels pixels :header header :lock lock :backend backend :state state :wire wire}]
                (try (let [cancel (schedule! #(locking lock (present! handle)))]
                       (swap! state assoc :cancel cancel)
                       handle)
                     (catch Throwable e (stop! handle) (throw e)))))
     :render! (fn [{:keys [lock state pixels] :as handle} image]
                (locking lock
                  (when-let [error (:failure @state)] (throw error))
                  (when-not (:open? @state) (throw (ex-info "Push 3 display is closed" {})))
                  (screen/encode! pixels image)
                  (when-not (:ready? @state)
                    (swap! state assoc :ready? true)
                    (present! handle))))
     :close! (fn [{:keys [lock] :as handle}] (locking lock (stop! handle)))}))

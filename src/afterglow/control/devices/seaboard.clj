(ns afterglow.control.devices.seaboard
  "ROLI Seaboard M's documented five expressive MIDI dimensions. The transport
  and Dashboard zone configuration are supplied explicitly; no device discovery
  or hardware initialization is assumed."
  (:require [afterglow.control.devices.mpe :as mpe]
            [afterglow.control.devices.session :as session]))

(def sources
  ["https://support.roli.com/en/support/solutions/articles/36000019142-what-midi-messages-do-seaboards-and-lightpads-transmit-"
   "https://support.roli.com/en/support/solutions/articles/36000576272-using-the-seaboard-m-with-ableton-live-12"])

(defn profile [options]
  (let [profile (mpe/profile (assoc options :axes #{:strike :pressure :glide :slide :lift}))]
    (-> profile (assoc :id :seaboard-m)
        (update :capabilities assoc :device :roli/seaboard-m :sources sources
                :protocol-verification :official-documentation :hardware-verified? false))))

(defn connect! [options]
  (session/open! (session/create (assoc options :profile (profile options)))))

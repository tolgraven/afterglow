(ns afterglow.sync.peer
  "Portable identity matching for paired Beat Link players."
  (:require [clojure.string :as str]))

(defn matches-pairing?
  "Match the player number and the saved hardware address when present.
  An address-only pairing uses the saved network address."
  [pairing peer]
  (and (some? (:device-number pairing))
       (= (:device-number pairing) (:device-number peer))
       (if-let [hardware-address (:hardware-address pairing)]
         (= (str/lower-case hardware-address) (some-> (:hardware-address peer) str/lower-case))
         (= (:address pairing) (:address peer)))))

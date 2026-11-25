(ns afterglow.output.retirement
  "Keep delivering configured physical off bytes after fixtures leave a patch."
  (:require [afterglow.render.frame :as frame]))

(defn- linear-address [[universe index]]
  (+ (* 512 (long universe)) (long index)))

(defn- unclaimed [off-bytes patch]
  (when (seq off-bytes)
    (let [fixtures (:fixtures patch)
          mapped (into #{} (for [f fixtures, channel (vals (:compiled-channels f))
                                 slot [(:coarse channel) (:fine channel)] :when slot] slot))
          reserved (into (sorted-map)
                         (keep (fn [{:keys [address universe footprint]}]
                                 (when footprint
                                   (let [start (linear-address [universe (dec address)])]
                                     [start (+ start (dec footprint))]))))
                         fixtures)]
      (into {} (remove (fn [[slot]]
                         (let [address (linear-address slot)
                               [_ last-reserved] (first (rsubseq reserved <= address))]
                           (or (mapped slot)
                               (and last-reserved (<= address last-reserved))))))
            off-bytes))))

(defn plan
  "Compile held output for a patch change. Reassigned channels and reserved
  fixture footprints immediately take ownership of their DMX slots."
  [prior previous-patch new-patch]
  (let [held (unclaimed (merge (:held prior) (frame/physical-off-bytes previous-patch)) new-patch)
        current (set (:universes new-patch))
        known (into (into (set (:known prior)) (:universes previous-patch)) current)
        retired (into {} (for [u known :when (not (current u))] [u (byte-array 512)]))
        overlays (reduce-kv (fn [result [u i] value]
                              (if-let [^bytes data (get retired u)]
                                (do (aset-byte data (int i) (unchecked-byte value)) result)
                                (update result u (fnil conj []) [i value]))) {} held)]
    {:known known :held held :retired retired :overlays overlays}))

(defn include-retired
  "Add withdrawn universes and retired slots on still-active universes. Clone
  changed buffers so a sink cannot mutate render history or idle templates."
  [{:keys [retired overlays]} universes]
  (let [packet (reduce-kv (fn [m u ^bytes data] (assoc m u (aclone data))) universes retired)]
    (reduce-kv (fn [m u entries]
                 (if-let [^bytes old (get m u)]
                   (let [^bytes data (aclone old)]
                     (doseq [[i value] entries] (aset-byte data (int i) (unchecked-byte value)))
                     (assoc m u data))
                   m))
               packet overlays)))

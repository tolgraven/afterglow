(require '[afterglow.channels :as channels]
         '[afterglow.effects.channel :as effects]
         '[afterglow.show :as show]
         '[afterglow.show-context :refer [*show* with-show]]
         '[clojure.data.json :as json]
         '[ola-clojure.ola-service :as ola])
(import '[com.google.protobuf ByteString])

(def slots {:normal-dimmer [1 1], :inverted-dimmer [1 2],
            :partial-dimmer [1 3], :inverted-pan [1 4], :inverted-head-red [1 5],
            :inverted-coarse [1 511], :inverted-fine [1 512], :untouched-universe [2 1]})

(defn unsigned-bytes [levels] (mapv #(bit-and 255 %) levels))

(defn capture [operation]
  (let [packets (atom [])]
    (with-redefs [ola/UpdateDmxData (fn [{:keys [universe ^ByteString data]} _]
                                    (swap! packets conj {:universe universe
                                                         :bytes (unsigned-bytes (.toByteArray data))}))]
      (operation))
    (vec (sort-by :universe @packets))))

(defn selected [packets]
  (let [by-universe (into {} (map (juxt :universe :bytes)) packets)]
    (into {} (map (fn [[name [universe slot]]]
                    [name (get-in by-universe [universe (dec slot)])])) slots)))

(defn packed-off-reference []
  (let [buffers {1 (byte-array 512), 2 (byte-array 512)}]
    (doseq [channel (channels/extract-channels (channels/expand-heads (show/all-fixtures))
                                              #(#{:dimmer :color} (:type %)))]
      (effects/apply-channel-value buffers channel 0))
    (selected (for [[universe bytes] buffers] {:universe universe :bytes (unsigned-bytes bytes)}))))

(let [[output revision] *command-line-args*]
  (with-show (show/show :universes [1 2])
    (show/patch-fixture! :head {:name "Mixed output"
                               :channels [(channels/dimmer 1)
                                          (channels/dimmer 2 :inverted-from 0)
                                          (channels/dimmer 3 :inverted-from 32)
                                          (assoc (channels/fine-channel :pan 4) :inverted-from 0)]
                               :heads [{:x 0 :y 0 :z 0
                                        :channels [(assoc (channels/color 5 :red) :inverted-from 0)]}]}
                         1 1)
    (show/patch-fixture! :fine-dimmer {:name "Fine inverted dimmer"
                                      :channels [(channels/dimmer 1 :fine-offset 2 :inverted-from 0)]}
                         1 511)
    (let [packets {:blackout-show (capture show/blackout-show)
                   :stop-all (with-redefs [show/active-shows (atom #{*show*})]
                               (capture show/stop-all!))
                   :blackout-universe (capture #(show/blackout-universe 1))}
          summary (update-vals packets selected)]
      (spit output (json/write-str {:revision revision :slots slots :packets packets
                                   :legacy-packer-reference (packed-off-reference)
                                   :selected summary}))
      (prn summary))))
(shutdown-agents)

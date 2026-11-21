(ns afterglow.sync.config
  "Portable per-show synchronization settings. Validation opens no resources."
  (:require [afterglow.control.clock :as clock]
            [afterglow.sync.session :refer [fail!]]))

(def defaults
  {:selected-source :manual
   :clock {:bpm 120.0 :beat 0.0 :playing? false :meter {:beats-per-bar 4 :bars-per-phrase 4}
           :timeout-ms 1500.0 :on-stale :hold}
   :midi {:enabled? false :source-id :midi-clock :input-index nil :output-index nil :control? false
          :expected-input-name nil :expected-output-name nil}
   :beat-link {:enabled? false :source-id :beat-link :status? false :align-bars? false :peer nil}
   :link {:enabled? false :source-id :ableton-link :port 17000 :follow-transport? true}})

(defn- bounded-int? [value low high] (and (integer? value) (<= low value high)))
(defn- text? [value limit] (and (string? value) (<= 1 (count value) limit)))
(defn- identifier? [value] (or (keyword? value) (text? value 128)))
(defn source-id [id]
  (when-not (identifier? id) (fail! :invalid-config "Clock source requires a bounded identity"))
  (keyword id))

(defn- check! [condition message]
  (when-not condition (fail! :invalid-config message)))

(defn- check-fields! [values allowed]
  (check! (and (map? values) (every? allowed (keys values))) "Unknown synchronization configuration field"))

(defn- check-midi! [{:keys [enabled? control? input-index output-index expected-input-name expected-output-name]}]
  (check! (and (boolean? control?)
               (every? #(or (nil? %) (bounded-int? % 0 4096)) [input-index output-index])
               (or (not enabled?) (some? input-index) (some? output-index))
               (every? #(or (nil? %) (and (string? %) (<= (count %) 512))) [expected-input-name expected-output-name]))
          "Invalid MIDI ports or control mode"))

(defn- check-peer! [{:keys [status? align-bars? peer]}]
  (check! (every? boolean? [status? align-bars?]) "Invalid Pro DJ Link mode")
  (when (some? peer)
    (check-fields! peer #{:device-number :device-name :address :hardware-address})
    (check! (and (bounded-int? (:device-number peer) 1 255)
                 (or (nil? (:device-name peer)) (text? (:device-name peer) 512))
                 (or (and (string? (:address peer)) (re-matches #"[0-9a-fA-F:.%]+" (:address peer)))
                     (and (string? (:hardware-address peer))
                          (re-matches #"(?i)[0-9a-f]{2}(:[0-9a-f]{2}){5}" (:hardware-address peer)))))
            "Invalid Pro DJ Link peer")))

(defn- check-link! [{:keys [port follow-transport?]}]
  (check! (and (bounded-int? port 1 65535) (boolean? follow-transport?)) "Invalid Ableton Link port or transport mode"))

(defn validate-config
  "Normalize the portable clock and source settings. Registered adapters may add
  a named section with :defaults and a :normalize function."
  ([input] (validate-config {} input))
  ([adapters input]
   (let [sections (merge (dissoc defaults :selected-source)
                         (into {} (map (fn [[id adapter]] [id (:defaults adapter)]) adapters)))
         selected (source-id (:selected-source input :manual))]
     (check-fields! input (conj (set (keys sections)) :selected-source))
     (let [config (reduce-kv
                   (fn [result id base]
                     (let [settings (get input id {})]
                       (check-fields! settings (set (keys base)))
                       (let [settings (merge base settings)]
                         (assoc result id
                                (if (= id :clock)
                                  (update settings :on-stale keyword)
                                  (do (check! (boolean? (:enabled? settings)) "Source enabled? must be boolean")
                                      (update settings :source-id source-id)))))))
                   {:selected-source selected} sections)
           ids (map :source-id (vals (dissoc config :selected-source :clock)))]
       (check! (and (= (count ids) (count (set ids))) (not-any? #{:manual} ids)
                    (contains? (conj (set ids) :manual) selected))
               "Each clock needs a unique source ID and the selected source must exist")
       (check-midi! (:midi config))
       (check-peer! (:beat-link config))
       (check-link! (:link config))
       (clock/new-state (assoc (:clock config) :selected-source selected))
       (reduce-kv (fn [result id adapter] (update result id (:normalize adapter identity))) config adapters)))))

(defn validate-state
  ([data] (validate-state {} data))
  ([adapters data]
   (when-not (and (map? data) (every? #{:version :config :wanted?} (keys data)) (= 1 (:version data))
                  (boolean? (get data :wanted? false)))
     (fail! :invalid-state "Invalid synchronization state document"))
   {:version 1 :config (validate-config adapters (:config data)) :wanted? (get data :wanted? false)}))

(ns afterglow.control.codecs.mpe
  "Pure MIDI 1.0 MPE receiver. Channels and zones remain explicit. Each active
  note has a generation identity; no ports, clock, callbacks or mutable cells."
  (:require [afterglow.control.codecs.midi :as midi]))

(def axes
  {:strike {:range [0 1] :phase :attack :message :note-on-velocity}
   :pressure {:range [0 1] :phase :continuous :message :channel-pressure}
   :glide {:range [-1 1] :phase :continuous :message :pitch-bend
           :meaning :relative-pitch-not-absolute-position}
   :slide {:range [0 1] :phase :continuous :message :cc74}
   :lift {:range [0 1] :phase :release :message :note-off-velocity}})

(def neutral {:pressure 0.0 :glide 0.0 :slide 0.5})
(defn initial-state [] {:counter 0 :voices {} :channels {}})

(defn compile-zone
  "Configure one MPE zone using zero-based channels. Manager is 0 (lower) or 15
  (upper), and members must be the contiguous adjacent range. No RPN negotiation
  or pitch range configuration is sent; pitch output is normalized, not semitones."
  [{:keys [manager-channel member-channels]}]
  (let [members (set member-channels) n (count members)
        expected (case manager-channel 0 (set (range 1 (inc n)))
                       15 (set (range (- 15 n) 15)) nil)]
    (when-not (and (coll? member-channels) (= n (count member-channels))
                   (<= 1 n 15) expected (= expected members))
      (throw (ex-info "MPE needs one explicit contiguous lower/upper zone" {:type ::invalid-zone})))
    {:manager-channel manager-channel :member-channels members}))

(defn- voice-event [type voice extra]
  (merge (select-keys voice [:voice-id :channel :note]) {:type type} extra))

(defn- end-note [state key lift reason]
  (if-let [voice (get-in state [:voices key])]
    (let [next (update state :voices dissoc key)
          channel (:channel voice)
          next (if (some #(= channel (:channel %)) (vals (:voices next))) next
                   (update next :channels dissoc channel))]
      {:state next :events [(voice-event :note-off voice {:axes {:lift lift} :reason reason})]})
    {:state state :events []}))

(defn- channel-expression [state channel axis value]
  (let [voices (filterv #(= channel (:channel %)) (vals (:voices state)))
        state (assoc-in state [:channels channel axis] value)]
    (if (> (count voices) 1)
      {:state state :events []
       :diagnostics [{:code :ambiguous-member-channel :channel channel :axis axis
                      :voice-ids (mapv :voice-id (sort-by :voice-id voices))}]}
      {:state state :events (mapv #(voice-event :axis % {:axis axis :value value}) voices)})))

(defn advance
  "Receive one complete channel message. Before-note expression is retained for
  the next note. After the last note ends, channel expression returns to neutral.
  Shared-channel polyphony is retained but expression is withheld as ambiguous.
  Manager messages are reported separately; they are never mistaken for a pad."
  [zone state bytes]
  (if-not (and (integer? (first bytes)) (<= 0x80 (first bytes) 0xef))
    {:state state :events []}
    (let [{:keys [type channel note value controller raw-value signed-value] :as event} (midi/decode bytes)
          key [channel note]
          manager? (= channel (:manager-channel zone))
          member? (contains? (:member-channels zone) channel)
          expression (case type
                       :channel-pressure [:pressure value]
                       :pitch-bend [:glide (/ signed-value (if (neg? signed-value) 8192.0 8191.0))]
                       :control-change (when (= controller 74) [:slide value]) nil)]
      (cond
        (and manager? expression)
        {:state state :events [{:type :zone-axis :channel channel :axis (first expression) :value (second expression)}]}
        (not member?) {:state state :events []}
        (= type :note-on)
        (let [ended (end-note state key 0.0 :retrigger)
              state (:state ended)
              counter (inc (:counter state))
              voice {:voice-id [channel note counter] :channel channel :note note}
              values (merge neutral (get-in state [:channels channel]) {:strike value})]
          {:state (-> state (assoc :counter counter) (assoc-in [:voices key] voice))
           :events (conj (:events ended) (voice-event :note-on voice {:axes values}))})
        (= type :note-off) (end-note state key value :released)
        expression (channel-expression state channel (first expression) (second expression))
        (and (= type :control-change) (#{120 123} controller))
        (reduce (fn [{:keys [state events]} key]
                  (let [ended (end-note state key 0.0 :all-notes-off)]
                    {:state (:state ended) :events (into events (:events ended))}))
                {:state state :events []}
                (sort (filter #(= channel (first %)) (keys (:voices state)))))
        :else {:state state :events []}))))

(ns afterglow.control.codecs.midi
  "Pure MIDI 1.0 channel-message codec. Channels are zero-based; no ports are opened.
  Decode accepts unsigned byte sequences, not running-status streams or SysEx.
  Values retain their raw representation alongside a normalized :value.")

(defn- bounded-int! [value low high field]
  (when-not (and (integer? value) (<= low value high))
    (throw (ex-info "MIDI value outside its integer range"
                    {:type ::invalid-message :field field :value value
                     :bounds [low high]})))
  value)

(defn decode
  "Decode one complete channel message. Malformed/unsupported messages throw.
  Note-on velocity zero becomes :note-off. Pitch bend retains :raw-value in
  [0,16383], :value in [0,1], and :signed-value in [-8192,8191]."
  [bytes]
  (let [message (vec (take 4 bytes))
        status (bounded-int! (first message) 128 239 :status)
        kind (bit-and status 0xf0)
        expected (if (#{0xc0 0xd0} kind) 2 3)]
    (when-not (= expected (count message))
      (throw (ex-info "MIDI channel message has incorrect length"
                      {:type ::invalid-message :expected expected :actual (count message)})))
    (doseq [byte (rest message)] (bounded-int! byte 0 127 :data))
    (let [[_ a b] message
          base {:channel (bit-and status 0x0f)}]
      (merge base
             (case kind
               0x80 {:type :note-off :note a :velocity b :value (/ b 127.0)}
               0x90 {:type (if (zero? b) :note-off :note-on)
                     :note a :velocity b :value (/ b 127.0)}
               0xa0 {:type :poly-pressure :note a :pressure b :value (/ b 127.0)}
               0xb0 {:type :control-change :controller a :raw-value b :value (/ b 127.0)}
               0xc0 {:type :program-change :program a :value (/ a 127.0)}
               0xd0 {:type :channel-pressure :pressure a :value (/ a 127.0)}
               0xe0 (let [raw (+ a (bit-shift-left b 7))]
                      {:type :pitch-bend :raw-value raw :signed-value (- raw 8192)
                       :value (/ raw 16383.0)}))))))

(defn encode
  "Encode normalized event type/channel and raw data fields into unsigned bytes.
  Raw :velocity, :pressure or :raw-value fields are required; normalized :value
  is presentation information and is never silently rounded back into MIDI."
  [{:keys [type channel note velocity controller raw-value pressure program]}]
  (bounded-int! channel 0 15 :channel)
  (let [data7 #(bounded-int! %1 0 127 %2)
        [status data]
        (case type
          :note-off [0x80 [(data7 note :note) (data7 velocity :velocity)]]
          :note-on [0x90 [(data7 note :note) (data7 velocity :velocity)]]
          :poly-pressure [0xa0 [(data7 note :note) (data7 pressure :pressure)]]
          :control-change [0xb0 [(data7 controller :controller) (data7 raw-value :raw-value)]]
          :program-change [0xc0 [(data7 program :program)]]
          :channel-pressure [0xd0 [(data7 pressure :pressure)]]
          :pitch-bend (let [v (bounded-int! raw-value 0 16383 :raw-value)]
                        [0xe0 [(bit-and v 0x7f) (bit-shift-right v 7)]])
          (throw (ex-info "Unsupported MIDI event type"
                          {:type ::invalid-message :event-type type})))]
    (into [(bit-or status channel)] data)))

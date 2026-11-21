(ns afterglow.control.codecs.push-2
  "Pure Push 2 MIDI helpers extracted from the existing Afterglow adapter.
  Protocol source: afterglow.controllers.ableton-push-2 send-sysex, set-pad-color,
  sign-velocity and pad mapping. Original adapter by James Elliott, EPL-2.0.
  These helpers have no native display, negotiation, hardware or port ownership.")

(def capabilities
  {:device :ableton/push-2
   :verification :source-derived
   :pads {:width 8 :height 8 :first-note 36 :last-note 99 :origin :bottom-left}
   :encoder-encoding :twos-complement-7-bit
   :led-palette {:entries 128 :components [:red :green :blue :white]
                 :component-bits 8}
   :display {:transport :native-wayang :implemented-here? false}
   :hardware-verified? false})

(defn- bounded! [value low high field]
  (when-not (and (integer? value) (<= low value high))
    (throw (ex-info "Invalid Push 2 protocol value"
                    {:type ::invalid-message :field field :value value :bounds [low high]})))
  value)

(defn pad-note [x y]
  (+ 36 (bounded! x 0 7 :x) (* 8 (bounded! y 0 7 :y))))

(defn pad-coordinates
  "Return local [x y], bottom-left origin. Non-pad notes return nil."
  [note]
  (bounded! note 0 127 :note)
  (when (<= 36 note 99)
    [(mod (- note 36) 8) (quot (- note 36) 8)]))

(defn signed-encoder [value]
  (bounded! value 0 127 :value)
  (if (>= value 64) (- value 128) value))

(defn sysex
  "Encode a Push 2 command (including its command byte), with full MIDI framing."
  [device-id command]
  (bounded! device-id 0 127 :device-id)
  (when-not (and (vector? command) (seq command))
    (throw (ex-info "Expected a nonempty Push 2 command vector" {:type ::invalid-message})))
  (doseq [byte command] (bounded! byte 0 127 :data))
  (into [0xf0 0x00 0x21 0x1d device-id 0x01] (conj command 0xf7)))

(defn palette-request [device-id index]
  (sysex device-id [0x04 (bounded! index 0 127 :index)]))

(def touch-strip-modes
  "Source-derived modes: host feedback, pitch-bend input, no automatic return.
  :default restores Push's point display and automatic center return."
  {:default 104 :level 65 :centered 81 :point 73 :off 67})

(defn touch-strip-mode [device-id mode]
  (let [value (get touch-strip-modes mode)]
    (when-not value
      (throw (ex-info "Unknown Push touch-strip mode" {:type ::invalid-message :mode mode})))
    (sysex device-id [0x17 value])))

(defn touch-strip-messages
  "Diff a source-derived strip feedback map {:mode keyword :value raw14}.
  :off explicitly clears the sixteen LED payload bytes; :default restores
  hardware control. Mode changes and pitch values are separate MIDI messages."
  [device-id before {:keys [mode value] :as after}]
  (let [mode-message (touch-strip-mode device-id mode)]
    (when-not (#{:off :default} mode) (bounded! value 0 16383 :value))
    (cond
      (= before after) []
      (= :default mode) [mode-message]
      (= :off mode) [mode-message (sysex device-id (into [0x19] (repeat 16 0)))]
      :else (cond-> []
              (not= (:mode before) mode) (conj mode-message)
              true (conj [0xe0 (bit-and value 0x7f) (bit-shift-right value 7)])))))

(defn palette-write
  "Encode palette RGBW as four integer 8-bit components, split low7/high1."
  [device-id index rgbw]
  (bounded! index 0 127 :index)
  (when-not (and (vector? rgbw) (= 4 (count rgbw)))
    (throw (ex-info "Palette requires four RGBW components" {:type ::invalid-message})))
  (sysex device-id
         (into [0x03 index]
               (mapcat (fn [value]
                         (bounded! value 0 255 :component)
                         [(bit-and value 0x7f) (bit-shift-right value 7)]))
               rgbw)))

(defn palette-reply
  "Decode a complete palette response for the supplied device. Foreign devices,
  model IDs and unrelated commands return nil; malformed matching replies throw."
  [device-id message]
  (bounded! device-id 0 127 :device-id)
  (let [message (vec (take 18 message))]
    (when (= [0xf0 0x00 0x21 0x1d device-id 0x01 0x04] (subvec message 0 (min 7 (count message))))
      (when-not (and (= 17 (count message)) (= 0xf7 (last message)))
        (throw (ex-info "Malformed Push 2 palette response" {:type ::invalid-message})))
      (let [index (bounded! (nth message 7) 0 127 :index)
            pairs (partition 2 (subvec message 8 16))
            rgbw (mapv (fn [[low high]]
                         (+ (bounded! low 0 127 :component-low)
                            (* 128 (bounded! high 0 1 :component-high)))) pairs)]
        {:index index :rgbw rgbw}))))

(defn pad-led-messages
  "Plan MIDI messages for one pad, preserving the explicitly supplied white
  palette component. Black uses note-off. RGB contains integer 8-bit values;
  actual sending, rate limits, palette acquisition/restoration belong to a shell."
  [device-id x y rgb white]
  (let [note (pad-note x y)]
    (bounded! device-id 0 127 :device-id)
    (bounded! white 0 255 :white)
    (when-not (and (vector? rgb) (= 3 (count rgb)))
      (throw (ex-info "Pad color requires three RGB components" {:type ::invalid-message})))
    (doseq [value rgb] (bounded! value 0 255 :component))
    (if (every? zero? rgb)
      [[0x80 note 0]]
      [(palette-write device-id note (conj rgb white)) [0x90 note note]])))

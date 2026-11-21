(ns afterglow.control.codecs.x-touch
  "Source-verified MCU-mode X-Touch/XT messages. Independent implementation of
  protocol facts, not copied remote-script code. See Tolglow docs/xtouch.md.
  No device discovery, transport, timer or background color cycling occurs here.")

(def reference
  {:repository "https://github.com/Kik07L/Behringer-X-Touch-for-ableton"
   :revision "7d31caf30cf4ffeeeb8369f1216436ff8789150b"
   :mode :mcu :verification :source-derived :hardware-verified? false})

(def palette [:black :red :green :yellow :blue :magenta :cyan :white])
(def palette-rgb [[0 0 0] [1 0 0] [0 1 0] [1 1 0] [0 0 1] [1 0 1] [0 1 1] [1 1 1]])
(def buttons {:bank-left 46 :bank-right 47 :channel-left 48 :channel-right 49
              :flip 50 :stop 93 :play 94 :record 95})

(defn- require! [condition message]
  (when-not condition (throw (ex-info message {:x-touch/error :invalid-message}))))
(defn- integer-in? [x low high] (and (integer? x) (<= low x high)))
(defn- normalized? [x] (and (number? x) (Double/isFinite (double x)) (<= 0 x 1)))
(defn- strip! [strip maximum] (require! (integer-in? strip 0 maximum) "Invalid MCU strip index") strip)
(defn device-id [extender?]
  (require! (boolean? extender?) "Extender selection must be boolean")
  (if extender? 0x15 0x14))

(defn signed-relative [value]
  (require! (integer-in? value 0 127) "Relative value must be a MIDI data byte")
  (* (if (bit-test value 6) -1 1) (bit-and value 0x3f)))

(defn decode
  "Decode complete channel messages to semantic physical controls. Unknown
  messages return nil. Note-off velocity never means a pressed button. Faders
  are 14-bit pitch bend on channels0..8; encoders are signed-bit CC16..23."
  [bytes]
  (require! (and (sequential? bytes) (every? #(integer-in? % 0 255) bytes)) "Expected unsigned MIDI bytes")
  (let [[status a b] bytes kind (when status (bit-and status 0xf0)) channel (when status (bit-and status 0x0f))]
    (when (#{0x80 0x90 0xb0 0xe0} kind)
      (require! (and (= 3 (count bytes)) (integer-in? a 0 127) (integer-in? b 0 127)) "Invalid channel message length/data")
      (cond
        (and (= kind 0xe0) (<= channel 8))
        (let [value (+ a (bit-shift-left b 7))]
          {:type :fader :strip channel :raw-value value :value (/ value 16383.0)})
        (and (#{0x80 0x90} kind) (zero? channel))
        (let [pressed? (and (= kind 0x90) (pos? b))]
          (if (<= 104 a 112) {:type :touch :strip (- a 104) :pressed? pressed?}
              {:type :button :note a :pressed? pressed?}))
        (and (= kind 0xb0) (zero? channel) (<= 16 a 23))
        {:type :encoder :strip (- a 16) :delta (signed-relative b)}
        (and (= kind 0xb0) (zero? channel) (= a 60))
        {:type :jog :delta (signed-relative b)}
        :else nil))))

(defn fader [strip value]
  (strip! strip 8)
  (require! (normalized? value) "Fader feedback must be in [0,1]")
  (let [raw (long (Math/round (* 16383.0 (double value))))]
    [(+ 0xe0 strip) (bit-and raw 127) (bit-and (bit-shift-right raw 7) 127)]))

(defn button-led [note state]
  (require! (integer-in? note 0 127) "Button note must be 0..127")
  (let [value ({:off 0 :on 127 :blink 1} state)]
    (require! (some? value) "LED state must be off/on/blink") [0x90 note value]))

(defn encoder-ring
  "MCU feedback positions0(off)..11 and documented single/boost-cut/wrap/spread
  modes. This accepts positions, not a pretend arbitrary-color ring value."
  ([strip position] (encoder-ring strip position :single))
  ([strip position mode]
   (strip! strip 7)
   (require! (integer-in? position 0 11) "Ring position must be 0..11")
   (let [mode-value ({:single 0 :boost-cut 1 :wrap 2 :spread 3} mode)]
     (require! (some? mode-value) "Unsupported ring mode")
     [0xb0 (+ 48 strip) (+ (* 16 mode-value) position)])))

(defn text
  "Write printable ASCII to a 56-column MCU display row. Replaces non-ASCII
  glyphs with '?'; callers own transliteration. No implicit padding/truncation."
  [extender? row column value]
  (require! (and (integer-in? row 0 1) (integer-in? column 0 55) (string? value)
                 (<= (count value) (- 56 column))) "Text exceeds the MCU display row")
  (into [0xf0 0 0 0x66 (device-id extender?) 0x12 (+ (* row 56) column)]
        (concat (map #(let [n (int %)] (if (<= 32 n 126) n 63)) value) [0xf7])))

(defn colors
  "Set eight native scribble-strip palette indices0..7. Main/XT device IDs are
  distinct; this is source-verified MCU behavior, not XCTL Ethernet/RGB support."
  [extender? values]
  (require! (and (vector? values) (= 8 (count values)) (every? #(integer-in? % 0 7) values))
            "Exactly eight native palette indices are required")
  (into [0xf0 0 0 0x66 (device-id extender?) 0x72] (conj values 0xf7)))

(defn palette-index
  "Nearest native color in normalized display RGB. Black is selected only for
  exact black, avoiding an unreadable dark approximation for active strips."
  [rgb]
  (require! (and (vector? rgb) (= 3 (count rgb)) (every? normalized? rgb)) "Display RGB must be three values in [0,1]")
  (if (every? zero? rgb) 0
    (first (sort-by (fn [index] (reduce + (map #(let [d (- %1 %2)] (* d d)) rgb (nth palette-rgb index))))
                    (range 1 8)))))

(defn temporal-color-frame
  "Pure research helper: one palette frame of simple temporal RGB duty mixing.
  Does not schedule/send anything. Hardware flicker/color accuracy and usable
  transport rates are unverified; normal profiles use static native colors."
  [rgb phase steps]
  (require! (and (vector? rgb) (= 3 (count rgb)) (every? normalized? rgb)
                 (integer-in? steps 2 256) (integer? phase) (<= 0 phase)) "Invalid temporal color sample")
  (reduce + (map-indexed (fn [axis value]
                          (if (< (mod phase steps) (Math/round (* (double steps) (double value))))
                            (bit-shift-left 1 axis) 0)) rgb)))

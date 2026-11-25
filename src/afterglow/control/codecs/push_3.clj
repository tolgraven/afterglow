(ns afterglow.control.codecs.push-3
  "Push 3 User Mode semantics grounded in Ableton's official manual. Numeric
  note/CC addresses must come from a caller's captures of that device/mode.
  This namespace deliberately contains no Push 2 addresses, SysEx or USB code."
  (:require [afterglow.control.codecs.midi :as midi]))

(def official-source "https://www.ableton.com/en/push/manual/#user-mode")

(def capabilities
  {:device :ableton/push-3 :mode :user
   :semantics-source official-source :semantics-verification :official-manual
   :address-source :caller-capture :automatic-address-map? false
   :implemented #{:pads :encoder-touches :relative-encoders :buttons :poly-pressure :mono-pressure :touch-strip}
   :supported-expression-modes #{:poly-aftertouch :mono-aftertouch}
   :mpe :not-implemented :led-protocol :unverified :display-protocol :unverified
   :automatic-user-mode? false :standalone-host-transport :unverified :hardware-verified? false})

(defn- require! [condition message data]
  (when-not condition (throw (ex-info message (assoc data :type ::invalid-layout)))))

(defn- int-in? [value low high] (and (integer? value) (<= low value high)))

(defn signed-encoder
  "Decode the official User Mode recommendation: Relative (lin. 2's comp.).
  1 is +1, 127 is -1, and 0 is stationary. No absolute encoder mode is inferred."
  [value]
  (require! (int-in? value 0 127) "Encoder data must be a MIDI data byte" {:value value})
  (if (< value 64) value (- value 128)))

(defn compile-layout
  "Validate explicit zero-based MIDI addresses and compile immutable lookups.
  :pads maps [x y] -> {:note n :channel c}; :encoder-touches maps logical IDs to
  note addresses; :encoders and :buttons map IDs to CC addresses; optional
  :touch-strip/:mono-pressure contain an explicitly captured :channel."
  [layout]
  (require! (map? layout) "A captured Push 3 layout map is required" {})
  (require! (every? #{:pads :encoder-touches :encoders :buttons :touch-strip :mono-pressure} (keys layout))
            "Unknown captured layout section" {:keys (keys layout)})
  (let [records (vec
                  (mapcat (fn [[section kind address-field]]
                            (let [entries (get layout section {})]
                              (require! (map? entries) "Layout sections must be maps" {:section section})
                              (for [[id address] entries]
                                (do
                                  (require! (if (= kind :pad)
                                              (and (vector? id) (= 2 (count id)) (every? #(int-in? % 0 7) id))
                                              (keyword? id))
                                            "Pads need [x y] in 0..7; other controls need keyword IDs" {:section section :id id})
                                  (require! (and (map? address) (= #{address-field :channel} (set (keys address)))
                                                 (int-in? (:channel address) 0 15) (int-in? (get address address-field) 0 127))
                                            "Capture a complete note/CC address and zero-based channel" {:section section :id id})
                                  {:kind kind :id id :address [(:channel address) (get address address-field)]
                                   :family (if (= address-field :note) :note :cc)}))))
                          [[:pads :pad :note] [:encoder-touches :encoder-touch :note]
                           [:encoders :encoder :controller] [:buttons :button :controller]]))]
    (doseq [family [:note :cc]
            :let [addresses (map :address (filter #(= family (:family %)) records))]]
      (require! (= (count addresses) (count (distinct addresses)))
                "Two controls share a captured MIDI address" {:family family}))
    (doseq [section [:touch-strip :mono-pressure] :let [address (get layout section)] :when address]
      (require! (and (map? address) (= #{:channel} (set (keys address))) (int-in? (:channel address) 0 15))
                "Capture a zero-based expression channel" {:section section}))
    {:layout layout
     :notes (into {} (map (juxt :address #(select-keys % [:kind :id])) (filter #(= :note (:family %)) records)))
     :controllers (into {} (map (juxt :address #(select-keys % [:kind :id])) (filter #(= :cc (:family %)) records)))}))

(defn capture
  "Add one real or synthetic sample to a layout without side effects. sample is
  {:kind :pad/:encoder-touch/:encoder/:button/:touch-strip/:mono-pressure,
   :id [x y] or keyword, :bytes [...]}. Tests use synthetic samples; this function
  does not certify the device that produced them. Releases cannot learn pads."
  [layout {:keys [kind id bytes]}]
  (let [event (midi/decode bytes)
        [section field expected] (case kind
                                   :pad [:pads :note :note-on]
                                   :encoder-touch [:encoder-touches :note :note-on]
                                   :encoder [:encoders :controller :control-change]
                                   :button [:buttons :controller :control-change]
                                   :touch-strip [:touch-strip nil :pitch-bend]
                                   :mono-pressure [:mono-pressure nil :channel-pressure]
                                   (throw (ex-info "Unknown capture kind" {:type ::invalid-layout :kind kind})))
        _ (require! (= expected (:type event)) "The sample does not match the control being captured" {:kind kind :event event})
        address (cond-> {:channel (:channel event)} field (assoc field (get event field)))
        next (if field (assoc-in layout [section id] address) (assoc layout section address))]
    (compile-layout next)
    next))

(defn decode
  "Decode only the documented User Mode message families at captured addresses.
  All output retains :midi source data. SysEx/realtime/unmapped messages are
  ignored, so a Push 2 packet can never be interpreted as a Push 3 handshake."
  [compiled bytes]
  (when (and (integer? (first bytes)) (<= 0x80 (first bytes) 0xef))
    (let [event (midi/decode bytes)
          {:keys [type channel note controller raw-value value]} event
          address [channel (or note controller)]
          note-control (get-in compiled [:notes address])
          cc-control (get-in compiled [:controllers address])
          base {:channel channel :value value :midi event}]
      (case type
        (:note-on :note-off)
        (when note-control
          (merge base {:type (:kind note-control) :control-id (:id note-control)
                       :pressed? (= type :note-on) :gesture-key [channel note]}))
        :control-change
        (when cc-control
          (merge base {:type (:kind cc-control) :control-id (:id cc-control)}
                 (if (= :encoder (:kind cc-control)) {:delta (signed-encoder raw-value)} {:pressed? (pos? raw-value)})))
        :poly-pressure
        (when (= :pad (:kind note-control))
          (merge base {:type :poly-pressure :control-id (:id note-control) :gesture-key [channel note]}))
        :channel-pressure
        (when (= channel (get-in compiled [:layout :mono-pressure :channel])) (assoc base :type :mono-pressure))
        :pitch-bend
        (when (= channel (get-in compiled [:layout :touch-strip :channel]))
          (assoc base :type :touch-strip :signed-value (:signed-value event)))
        nil))))

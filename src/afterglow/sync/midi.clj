(ns afterglow.sync.midi
  "Java MIDI port ownership, MIDI clock decoding and per-channel observations."
  (:require [afterglow.control.clock :as clock]
            [afterglow.control.codecs.midi :as midi-codec]
            [afterglow.sync.session :refer [apply-clock! emit! fail!]])
  (:import [javax.sound.midi MidiSystem MidiDevice MidiMessage Receiver ShortMessage]))

(defn transport
  "Explicit input/output acquisition using Java MIDI. Either direction may be
  omitted. Previously open devices remain open; only this adapter's handles and
  newly opened devices are closed. No enumeration/opening happens at creation."
  [config clock-ms]
  {:open!
   (fn [receive!]
     (let [infos (vec (MidiSystem/getMidiDeviceInfo)) acquired (atom []) opened (atom []) handles (atom {})]
       (try
         (doseq [[direction index expected] [[:input (:input-index config) (:expected-input-name config)]
                                             [:output (:output-index config) (:expected-output-name config)]]
                 :when (some? index)]
           (let [info (get infos index)]
             (when-not info (fail! :missing-port "Selected MIDI port is no longer available"))
             (when (and expected (not= expected (.getName info))) (fail! :changed-port "Selected MIDI port name changed"))
             (let [^MidiDevice device (or (some #(when (= index (:index %)) (:device %)) @acquired) (MidiSystem/getMidiDevice info))]
               (swap! acquired conj {:index index :device device})
               (when-not (.isOpen device) (.open device) (swap! opened conj device))
               (if (= direction :input)
                 (let [transmitter (.getTransmitter device)]
                   (swap! handles assoc :transmitter transmitter)
                   (.setReceiver transmitter
                     (reify Receiver
                       (send [_ message timestamp]
                         (receive! {:type :midi/message :source-id (:source-id config) :time-ms (clock-ms)
                                    :device-timestamp-us timestamp
                                    :bytes (mapv #(bit-and 255 %) (take (.getLength ^MidiMessage message) (.getMessage ^MidiMessage message)))}))
                       (close [_] nil))))
                 (swap! handles assoc :receiver (.getReceiver device))))))
         (assoc @handles :owned-devices @opened)
         (catch Exception error
           (doseq [resource (vals @handles)] (try (.close ^java.lang.AutoCloseable resource) (catch Exception _)))
           (doseq [^MidiDevice device @opened] (try (.close device) (catch Exception _)))
           (throw error)))))
   :send! (fn [{:keys [receiver]} messages]
            (when-not receiver (fail! :no-midi-output "No MIDI output is configured"))
            (doseq [bytes messages]
              (let [[status a b] bytes]
                (.send ^Receiver receiver (doto (ShortMessage.) (.setMessage (int status) (int (or a 0)) (int (or b 0)))) -1))))
   :close! (fn [{:keys [transmitter receiver owned-devices]}]
             (doseq [resource [transmitter receiver]] (when resource (try (.close ^java.lang.AutoCloseable resource) (catch Exception _))))
             (doseq [^MidiDevice device owned-devices] (.close device)))})

(defn observe-midi! [manager run event transport origin at-ms]
  (when (and (#{:note-on :note-off :cc} (:type event)) (not (:feedback? event)))
    (let [source (or (:source-id event) (get-in @(:state manager) [:config transport :source-id]))
          note? (contains? event :note) value (if note? (get event :velocity 0) (:value event))
          off? (or (= :note-off (:type event)) (and (= :note-on (:type event)) (zero? value)))
          source-name (if (keyword? source) (subs (str source) 1) (str source))
          port-id (str (name transport) "/" source-name "/ch/" (:channel event) "/"
                       (if note? "note/" "cc/") (if note? (:note event) (:controller event)))]
      (when-not (and (integer? (:channel event)) (<= 1 (:channel event) 16)
                     (every? #(and (integer? %) (<= 0 % 127)) [value (if note? (:note event) (:controller event))]))
        (fail! :invalid-midi "Malformed MIDI observation"))
      (emit! manager run
             {:type :sync/observation
              :observation {:source-id port-id :event-id (str (:id run) "/observation/" (swap! (:event-sequence run) inc))
                            :observed-at-ms at-ms :kind :midi :sync-run-id (:id run)
                            :port (merge {:transport transport :source-id source :channel (:channel event)
                                          :signal (if note? :velocity :cc)} (select-keys event [:note :controller]))
                            :value (if off? 0 value) :gate? (not off?) :confidence 1.0
                            :origin origin}}))))

(defn receive! [manager run event at control!]
  (let [config (:config @(:state manager))]
    (if-let [decoded (clock/decode-midi (:bytes event))]
      (apply-clock! manager run (merge decoded (select-keys event [:source-id :time-ms])))
      (when (< (first (:bytes event)) 0xf0)
        (let [decoded (midi-codec/decode (:bytes event))
              captured-at (:time-ms event at)
              event (merge decoded {:channel (inc (:channel decoded)) :source-id (:source-id event)}
                           (when (= :control-change (:type decoded)) {:type :cc :value (:raw-value decoded)}))]
          (when (#{:note-on :note-off :cc} (:type event))
            (observe-midi! manager run event :midi :midi-input captured-at)
            (when (get-in config [:midi :control?]) (control! manager run event))))))))

(ns afterglow.control.clock
  "Pure selected-source musical clocks. Adapters supply timestamps and event data;
  this namespace never reads time, opens MIDI/network resources or changes a show.
  MIDI clock is 24 pulses per quarter note; SPP units are six pulses (1/16 note)."
  (:require [afterglow.time :as time]))

(defn- finite? [x] (time/finite-number? x))
(defn- identifier? [x] (or (keyword? x) (and (string? x) (<= 1 (count x) 128))))
(defn- fail! [message] (throw (ex-info message {:clock/error :invalid-input})))
(defn- clamp [x low high] (max low (min high x)))
(defn- median [values]
  (let [values (vec (sort values)) n (count values)]
    (if (odd? n) (nth values (quot n 2)) (/ (+ (nth values (dec (quot n 2))) (nth values (quot n 2))) 2.0))))

(defn new-state
  "Create explicit clock state. A stale selected source either :hold (default,
  freezes after timeout) or :freewheel (continues with zero confidence). A source
  is never silently replaced with a different peer. Manual transport stays host
  owned; the stored manual clock is only an explicit initial/reference value."
  ([] (new-state {}))
  ([options]
   (let [opts (merge {:selected-source :manual :time-ms 0.0 :bpm 120.0 :beat 0.0 :playing? false
                     :meter time/default-meter :timeout-ms 1500.0 :on-stale :hold
                     :interval-window 24 :bpm-range [20.0 400.0] :source-limit 32} options)
         [low high] (:bpm-range opts)]
     (when-not (and (identifier? (:selected-source opts))
                    (every? finite? ((juxt :time-ms :beat :bpm :timeout-ms) opts))
                    (<= 0 (:time-ms opts)) (<= 0 (:beat opts)) (pos? (:timeout-ms opts))
                    (boolean? (:playing? opts)) (#{:hold :freewheel} (:on-stale opts))
                    (every? finite? [low high]) (< 0 low high 1000) (<= low (:bpm opts) high)
                    (integer? (:interval-window opts)) (<= 6 (:interval-window opts) 96)
                    (integer? (:source-limit opts)) (<= 1 (:source-limit opts) 128))
       (fail! "Invalid clock options"))
     (let [meter (time/normalize-meter (:meter opts))]
       {:version 1 :selected-source (:selected-source opts) :selection-epoch 0 :revision 0
        :options (assoc opts :meter meter)
        :sources {:manual {:kind :manual :time-ms (:time-ms opts) :last-event-ms (:time-ms opts)
                           :beat (double (:beat opts)) :bpm (double (:bpm opts)) :playing? (:playing? opts)
                           :meter meter :confidence 1.0 :source-epoch 0 :connected? true}}}))))

(defn decode-midi
  "Decode one complete MIDI system message; channel messages return nil.
  Real-time clock/start/continue/stop and 14-bit Song Position Pointer are
  supported. Bytes are unsigned; malformed supported messages throw."
  [bytes]
  (let [bytes (vec (take 4 bytes)) status (first bytes)]
    (when-not (and (seq bytes) (every? #(and (integer? %) (<= 0 % 255)) bytes))
      (fail! "MIDI clock input must be unsigned bytes"))
    (cond
      (#{0xf8 0xfa 0xfb 0xfc} status)
      (do (when-not (= 1 (count bytes)) (fail! "MIDI real-time messages have one byte"))
          {:type ({0xf8 :midi/clock 0xfa :midi/start 0xfb :midi/continue 0xfc :midi/stop} status)})
      (= status 0xf2)
      (do (when-not (and (= 3 (count bytes)) (every? #(<= 0 % 127) (rest bytes)))
            (fail! "Song Position Pointer requires two 7-bit data bytes"))
          {:type :midi/song-position :sixteenths (+ (second bytes) (bit-shift-left (nth bytes 2) 7))})
      :else nil)))

(defn- position [source at-ms]
  (+ (:beat source) (if (and (:playing? source) (not (:awaiting-first-tick? source)))
                     (* (/ (max 0.0 (- at-ms (:time-ms source))) 60000.0) (:bpm source)) 0.0)))

(defn snapshot
  "Project the selected source at an explicit logical time. Returns :clock nil
  while awaiting an unseen source. A stale source is labeled and never gets a
  fabricated confidence. No state is changed by projection."
  [state at-ms]
  (when-not (and (= 1 (:version state)) (finite? at-ms) (<= 0 at-ms)) (fail! "Invalid clock snapshot time"))
  (let [id (:selected-source state) source (get-in state [:sources id])
        base {:selected-source id :selection-epoch (:selection-epoch state) :revision (:revision state)}]
    (if-not source (assoc base :status :waiting :clock nil)
        (let [manual? (= id :manual) age (max 0.0 (- at-ms (:last-event-ms source)))
              stale? (and (not manual?) (or (false? (:connected? source)) (> age (get-in state [:options :timeout-ms]))))
              hold? (and stale? (= :hold (get-in state [:options :on-stale])))
              projected-at (if hold? (min at-ms (+ (:last-event-ms source) (get-in state [:options :timeout-ms]))) at-ms)
              status (cond manual? :manual (false? (:connected? source)) :disconnected stale? :stale
                           (not (:playing? source)) :paused :else :locked)]
          (assoc base :status status
                 :clock {:time-ms at-ms :beat (position source projected-at) :bpm (:bpm source)
                         :playing? (boolean (and (:playing? source) (not hold?) (not (:awaiting-first-tick? source))))
                         :meter (:meter source) :source id :source-kind (:kind source)
                         :source-epoch (:source-epoch source) :confidence (if stale? 0.0 (:confidence source))
                         :source-age-ms age :source-time-ms (:time-ms source)
                         :stale? (boolean stale?) :phase-kind (get source :phase-kind :absolute)})))))

(defn select-source
  "Select a source identity explicitly, preserving every source's independent
  state. Unknown identities wait for an event; no previous source is substituted."
  [state source-id]
  (when-not (identifier? source-id) (fail! "Clock source must have a stable identity"))
  (if (= source-id (:selected-source state)) state
      (-> state (assoc :selected-source source-id) (update :selection-epoch inc) (update :revision inc))))

(defn- initial-source [state kind at-ms]
  (merge (select-keys (get-in state [:sources :manual]) [:bpm :meter])
         {:kind kind :time-ms at-ms :last-event-ms at-ms :beat 0.0 :playing? false :confidence 0.0
          :source-epoch 0 :connected? true :tick-position 0 :awaiting-first-tick? true :intervals []}))

(defn- midi-step [state source event]
  (let [at (:time-ms event) opts (:options state)]
    (case (:type event)
      :midi/start (-> source (assoc :playing? true :beat 0.0 :tick-position 0 :awaiting-first-tick? true
                                    :time-ms at :last-tick-ms nil :intervals [] :confidence 0.0 :phase-kind :midi-position)
                      (update :source-epoch inc))
      :midi/continue (assoc source :playing? true :awaiting-first-tick? true :time-ms at :last-tick-ms nil)
      :midi/stop (assoc source :playing? false :awaiting-first-tick? false :time-ms at)
      :midi/song-position
      (let [sixteenths (:sixteenths event)]
        (when-not (and (integer? sixteenths) (<= 0 sixteenths 16383)) (fail! "Invalid MIDI Song Position Pointer"))
        (-> source (assoc :beat (/ sixteenths 4.0) :tick-position (* sixteenths 6) :time-ms at
                         :awaiting-first-tick? true :phase-kind :midi-position)
            (update :source-epoch inc)))
      :midi/clock
      (let [last-time (:last-tick-ms source) interval (when last-time (- at last-time))
            [low high] (:bpm-range opts)
            in-range? (and interval (<= (/ 60000.0 (* 24 high)) interval (/ 60000.0 (* 24 low))))
            intervals (if in-range? (vec (take-last (:interval-window opts) (conj (:intervals source) interval)))
                          (if (and interval (> interval (:timeout-ms opts))) [] (:intervals source)))
            period (when (seq intervals) (median intervals))
            deviation (when period (median (map #(Math/abs (double (- % period))) intervals)))
            confidence (if period (* (min 1.0 (/ (count intervals) (double (:interval-window opts))))
                                    (clamp (- 1.0 (* 4.0 (/ deviation period))) 0.0 1.0)) 0.0)
            tick (if (:playing? source) (+ (:tick-position source) (if (:awaiting-first-tick? source) 0 1)) (:tick-position source))]
        (cond-> (assoc source :time-ms at :last-tick-ms at :intervals intervals :confidence confidence
                       :tick-position tick :beat (/ tick 24.0) :phase-kind :midi-position)
          period (assoc :bpm (/ 60000.0 (* 24 period)))
          (:playing? source) (assoc :awaiting-first-tick? false))))))

(defn apply-event
  "Apply timestamped {:source-id :type :time-ms ...} data and return
  {:state :accepted? :reason?}. MIDI events use decode-midi types. External
  :clock events carry absolute :beat/:bpm/:playing?/:confidence and optional
  :meter/:kind. Beat Link :beat-link/beat gives BPM and optional 1-based bar beat;
  :beat-link/status updates tempo/playing without pretending an integer status
  beat number is a fractional playhead. :source/lost freezes the last projection.
  Out-of-order source events and duplicate clock ticks are ignored."
  [state {:keys [source-id type time-ms] :as event}]
  (when-not (and (= 1 (:version state)) (identifier? source-id) (finite? time-ms) (<= 0 time-ms)
                 (#{:midi/start :midi/continue :midi/stop :midi/clock :midi/song-position
                    :beat-link/beat :beat-link/status :clock :source/lost} type))
    (fail! "Invalid timestamped clock event"))
  (let [old (get-in state [:sources source-id])
        kind (cond (= "midi" (namespace type)) :midi-clock (= "beat-link" (namespace type)) :beat-link
                   :else (get event :kind :external))
        source (or old (initial-source state kind time-ms))
        stale? (and old (< time-ms (:last-event-ms old)))
        duplicate? (and old (= type :midi/clock) (= time-ms (:last-tick-ms old)))
        duplicate-beat? (and old (= type :beat-link/beat) (:last-beat-ms old)
                             (< (- time-ms (:last-beat-ms old)) (* 0.35 (/ 60000.0 (:bpm old)))))]
    (cond
      stale? {:state state :accepted? false :reason :out-of-order}
      duplicate? {:state state :accepted? false :reason :duplicate-tick}
      duplicate-beat? {:state state :accepted? false :reason :duplicate-beat}
      (and (nil? old) (>= (count (:sources state)) (get-in state [:options :source-limit])))
      {:state state :accepted? false :reason :source-limit}
      :else
      (let [next-source
            (cond
              (= "midi" (namespace type)) (midi-step state source event)
              (= type :source/lost) (assoc source :beat (position source time-ms) :time-ms time-ms :playing? false :connected? false)
              (= type :clock)
              (do
                (when-not (and (every? finite? ((juxt :beat :bpm :confidence) event)) (<= 0 (:beat event))
                               (< 0 (:bpm event) 1000) (<= 0 (:confidence event) 1) (boolean? (:playing? event)))
                  (fail! "External clock requires finite beat, bpm, confidence and playing state"))
                (merge source (select-keys event [:beat :bpm :playing? :confidence :kind])
                       {:time-ms time-ms :awaiting-first-tick? false :phase-kind :absolute
                        :meter (time/normalize-meter (or (:meter event) (:meter source)))}))
              (= type :beat-link/status)
              (do
                (when-not (and (boolean? (:playing? event))
                               (or (nil? (:bpm event)) (and (finite? (:bpm event)) (< 0 (:bpm event) 1000))))
                  (fail! "Invalid Beat Link player status"))
                (cond-> (assoc source :beat (position source time-ms) :time-ms time-ms :playing? (:playing? event))
                  (:bpm event) (assoc :bpm (:bpm event))))
              (= type :beat-link/beat)
              (let [bpm (:bpm event) bar (:beat-within-bar event)
                    _ (when-not (and (finite? bpm) (< 0 bpm 1000)
                                     (or (nil? bar) (and (integer? bar) (<= 1 bar 4))))
                        (fail! "Invalid Beat Link beat data"))
                    predicted (position source time-ms)
                    beat (if (:seen-beat? source) (max (inc (:last-beat-number source)) (long (Math/round predicted)))
                             (if (and (:align-bars? event) (:bar-meaningful? event) bar) (dec bar) 0))
                    beat (if (and (:align-bars? event) (:bar-meaningful? event) bar
                                  (= 4 (get-in source [:meter :beats-per-bar])))
                           (+ beat (mod (- (dec bar) (mod beat 4)) 4)) beat)]
                (assoc source :beat (double beat) :time-ms time-ms :bpm bpm :playing? true
                       :awaiting-first-tick? false :seen-beat? true :phase-kind :beat-phase
                       :last-beat-ms time-ms :last-beat-number beat
                       :confidence (if (:bar-meaningful? event) 0.95 0.8)
                       :beat-within-bar bar :bar-meaningful? (boolean (:bar-meaningful? event)))))
            next-source (cond-> (assoc next-source :last-event-ms time-ms)
                          (not= type :source/lost) (assoc :connected? true))]
        {:state (-> state (assoc-in [:sources source-id] next-source) (update :revision inc)) :accepted? true}))))

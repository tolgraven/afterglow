(ns afterglow.render.presentation
  "Pure, timestamped output presentation after effect evaluation and DMX packing.

  The host owns completion admission and presentation scheduling. This namespace
  never evaluates effects or changes the canonical show state. Packet bytes are
  immutable vectors; materialize creates exclusively owned transport arrays."
  (:require [afterglow.render.frame :as frame]
            [afterglow.render.photometry :as photometry]))

(deftype PackedChannel [^long coarseUniverse ^long coarseIndex ^long fineUniverse ^long fineIndex ^boolean inverted ^boolean fade])

(def ^:private emitters (set (keys photometry/emitter-spectrum)))

(def ^:private emission-attributes (conj emitters :dimmer))

(def ^:private continuous (into emission-attributes #{:pan :tilt :focus :zoom}))

(defn- fail! [message data] (throw (ex-info message (assoc data :type ::invalid-presentation))))

(defn- finite? [x] (and (number? x) (Double/isFinite (double x))))

(defn- natural? [x] (and (integer? x) (<= 0 x Long/MAX_VALUE)))

(defn- nonnegative? [x] (and (finite? x) (<= 0 x)))

(defn- unit [x] (max 0.0 (min 1.0 (double x))))

(defn- linear-channel? [attribute channel]
  (and (contains? continuous attribute)
       (not= :hold (:presentation channel))
       (or (nil? (:inverted-from channel)) (zero? (:inverted-from channel)))
       (every? #(or (nil? (get channel %)) (= :linear (get channel %)))
               [:curve :transfer :dimming-curve])
       (not-any? #(some? (get channel %)) [:functions :capabilities :ranges])))

(defn compile-plan
  "Build immutable channel policy from frame/compile-patch or fixture data.

  Known linear dimmer/RGBW/emitter, pan/tilt/focus/zoom channels interpolate.
  Unknown/discrete channels, function ranges, nonlinear curves and partial
  inversions hold. :presentation :hold explicitly opts a channel out. Fade uses
  a fixture's linear hardware dimmer once, else its linear emitter channels.
  Coarse/fine interpolation uses the full 16-bit word across both universes."
  [patch-or-fixtures]
  (let [patch (if (vector? patch-or-fixtures) (frame/compile-patch patch-or-fixtures) patch-or-fixtures)]
    (when-not (= :afterglow.render.frame/patch (:type patch))
      (fail! "Expected a compiled patch or fixture vector" {}))
    (let [channels
          (vec (mapcat
           (fn [fixture]
             (let [channels (:compiled-channels fixture)
                   dimmer? (boolean (when-let [dimmer (:dimmer channels)] (linear-channel? :dimmer dimmer)))]
               (for [[attribute channel] (sort-by key channels)
                     :when (linear-channel? attribute channel)]
                 {:fixture-id (:id fixture) :attribute attribute
                  :coarse (:coarse channel) :fine (:fine channel)
                  :inverted? (= 0 (:inverted-from channel))
                  :fade? (if dimmer? (= :dimmer attribute) (contains? emitters attribute))})))
           (:fixtures patch)))
          indices (zipmap (:universes patch) (range))]
      {:type ::plan :universes (:universes patch) :channels channels
       ::fixtures (:by-id patch) ::universe-indices indices
       :idle-universes (reduce-kv (fn [buffers address value] (assoc-in buffers address value))
                                  (zipmap (:universes patch) (repeat (vec (repeat 512 0))))
                                  (frame/physical-off-bytes patch))
       ::packed (mapv (fn [{:keys [coarse fine inverted? fade?]}]
                        (PackedChannel. (long (get indices (first coarse))) (long (second coarse))
                                        (long (if fine (get indices (first fine)) -1))
                                        (long (if fine (second fine) -1)) inverted? fade?)) channels)})))

(defn- invalid-universe! [id]
  (fail! "Each universe must contain exactly 512 byte values" {:universe id}))

(defn- validate-size [id size]
  (when-not (= 512 size) (invalid-universe! id)))

(defn- freeze-bytes [id ^bytes values]
  (validate-size id (alength values))
  (loop [index 0 result (transient [])]
    (if (= index 512)
      (persistent! result)
      (recur (inc index) (conj! result (bit-and (aget values index) 255))))))

(defn- normalize-vector [id values]
  (validate-size id (count values))
  ;; Each comparison can run without boxing doubles in the per-slot scan.
  (let [signed? (reduce (fn [seen-negative? value]
                          (when-not (and (integer? value) (<= -128 value) (<= value 255))
                            (invalid-universe! id))
                          (or seen-negative? (neg? (long value))))
                        false values)]
    (if signed? (mapv #(bit-and (int %) 255) values) values)))

(defn- immutable-universes [universes]
  (when-not (and (map? universes) (every? natural? (keys universes)))
    (fail! "Universes must be a map of nonnegative integer IDs" {}))
  (reduce-kv (fn [result id values]
               (assoc result id
                      (cond
                        (bytes? values) (freeze-bytes id values)
                        (vector? values) (normalize-vector id values)
                        :else (fail! "Packet bytes must be an owned byte array or immutable vector"
                                     {:universe id}))))
             (sorted-map) universes))

(defn freeze-frame
  "Copy completed renderer buffers into a portable immutable packet.

  metadata has nonnegative integer :epoch/:frame-id, monotonic physical
  :time-ms (sample/scheduled time) and :completed-at-ms. Completion cannot
  precede the render start. An explicit :started-at-ms permits a physical
  deadline sample to finish early. Rejected :edge-tracking followers retain
  their emission cuts for buffered presentation. Input buffer ownership must
  remain exclusive during copy."
  [metadata rendered]
  (let [{:keys [epoch frame-id time-ms completed-at-ms started-at-ms]} metadata
        cuts (or (::tracking-cuts rendered)
                 (when-let [reports (:edge-tracking rendered)]
                   (into #{} (keep (fn [{:keys [follower reason]}] (when reason follower))) reports)))]
    (when-not (and (natural? epoch) (natural? frame-id) (nonnegative? time-ms)
                   (nonnegative? completed-at-ms)
                   (if (some? started-at-ms)
                     (and (nonnegative? started-at-ms) (<= started-at-ms time-ms)
                          (<= started-at-ms completed-at-ms))
                     (<= time-ms completed-at-ms)))
      (fail! "Invalid completed frame identity or timestamps" {:metadata metadata}))
    (cond-> {:epoch epoch :frame-id frame-id :time-ms time-ms :completed-at-ms completed-at-ms
             :universes (immutable-universes (:universes rendered))}
      (some? started-at-ms) (assoc :started-at-ms started-at-ms)
      (seq cuts) (assoc ::tracking-cuts (set cuts)))))

(defn- transport-bytes [values]
  (let [result (byte-array 512)]
    (dotimes [index 512]
      (aset result index (unchecked-byte (nth values index))))
    result))

(defn materialize
  "Return fresh transport-owned byte arrays. Never share returned arrays between
  a mutating transport and another consumer. The immutable packet is unchanged."
  [packet]
  (assoc packet :universes
         (into (sorted-map)
               (for [[id values] (immutable-universes (:universes packet))]
                 [id (transport-bytes values)]))))

(defn new-state
  "Create a policy with empty history. All timing here is physical milliseconds.

  :mode is :direct, :hold-fade or :buffered-interpolation; default :direct.
  :period-ms defaults 25 (40 Hz), :latency-ms defaults one period, and
  :fade-ms defaults 100 after one period without a new source frame. Buffered
  mode delays the target timeline by latency. History is bounded to three completed packets; an overproducing worker may
  exhaust interpolation history. No future frame is extrapolated."
  ([plan] (new-state plan {}))
  ([plan options]
   (let [{:keys [epoch mode period-ms latency-ms fade-ms] :as options}
         (merge {:epoch 0 :mode :direct :period-ms 25.0 :fade-ms 100.0} options)
         latency-ms (or latency-ms period-ms)]
     (when-not (and (= ::plan (:type plan)) (natural? epoch)
                    (#{:direct :hold-fade :buffered-interpolation} mode)
                    (finite? period-ms) (pos? period-ms)
                    (finite? latency-ms) (<= 0 latency-ms (* 2 period-ms))
                    (finite? fade-ms) (pos? fade-ms))
       (fail! "Invalid presentation plan or policy" {:options options}))
     {:plan plan :options (assoc options :latency-ms latency-ms) :history []
      :last-presented-at-ms nil :accepted 0 :dropped 0})))

(defn complete
  "Admit an immutable completion; return {:state ... :accepted? ... :reason ...}.
  Wrong epoch and reversed/duplicate frame identity or timestamp are dropped.
  Strictly increasing sample times prevent a late old worker overwriting newer
  output. Completing a packet never presents it or re-applies effect state."
  [state packet]
  (when-not (and (map? packet) (every? vector? (vals (:universes packet))))
    (fail! "complete requires a frozen immutable packet" {}))
  (let [packet (freeze-frame packet packet)
        previous (peek (:history state))
        reason (cond
                 (not= (get-in state [:options :epoch]) (:epoch packet)) :epoch
                 (not= (set (get-in state [:plan :universes])) (set (keys (:universes packet)))) :patch
                 (and previous (or (<= (:frame-id packet) (:frame-id previous))
                                   (<= (:time-ms packet) (:time-ms previous)))) :stale
                 (and previous (< (:completed-at-ms packet) (:completed-at-ms previous))) :completion-clock)]
    (if reason
      {:state (update state :dropped inc) :accepted? false :reason reason}
      {:state (-> state (update :accepted inc)
                  (update :history #(vec (take-last 3 (conj % packet)))))
       :accepted? true})))

(defn- indexed [plan universes]
  (object-array (map universes (:universes plan))))

(defn- scratch [^objects values]
  (let [result (object-array (alength values))]
    (dotimes [i (alength values)] (aset result i (transient (aget values i))))
    result))

(defn- immutable [plan ^objects values]
  (into (sorted-map) (map-indexed (fn [i id] [id (persistent! (aget values i))]) (:universes plan))))

(defn- read-word ^double [^objects universes ^PackedChannel channel]
  (let [^clojure.lang.IPersistentVector coarse (aget universes (int (.-coarseUniverse channel)))
        value (double (.nth coarse (int (.-coarseIndex channel))))
        value (if (neg? (.-fineUniverse channel)) value
                  (let [^clojure.lang.IPersistentVector fine (aget universes (int (.-fineUniverse channel)))]
                    (/ (+ (* value 256.0) (double (.nth fine (int (.-fineIndex channel))))) 257.0)))]
    (if (.-inverted channel) (- 255.0 value) value)))

(defn- write-word! [^objects universes ^PackedChannel channel ^double value]
  (let [value (max 0.0 (min 255.0 value))
        value (if (.-inverted channel) (- 255.0 value) value)
        coarse-universe (int (.-coarseUniverse channel))
        ^clojure.lang.ITransientVector coarse (aget universes coarse-universe)]
    (if (neg? (.-fineUniverse channel))
      (aset universes coarse-universe (.assocN coarse (int (.-coarseIndex channel)) (Math/round value)))
      (let [word (Math/round (* 257.0 value))
            whole (unsigned-bit-shift-right word 8) fraction (bit-and word 255)
            fine-universe (int (.-fineUniverse channel))]
        (aset universes coarse-universe (.assocN coarse (int (.-coarseIndex channel)) whole))
        (let [^clojure.lang.ITransientVector fine (aget universes fine-universe)]
          (aset universes fine-universe (.assocN fine (int (.-fineIndex channel)) fraction)))))))

(defn- copy-tracking-emission! [plan ^objects source ^objects result followers]
  (doseq [id followers
          [attribute channel] (:compiled-channels (get (::fixtures plan) id))
          :when (contains? emission-attributes attribute)
          [universe index] (keep channel [:coarse :fine])]
    (let [i (int (get (::universe-indices plan) universe))
          ^clojure.lang.IPersistentVector from (aget source i)
          ^clojure.lang.ITransientVector to (aget result i)]
      (aset result i (.assocN to (int index) (.nth from (int index)))))))

(defn- interpolate [plan left right weight]
  (cond
    (<= weight 0) (:universes left)
    (>= weight 1) (:universes right)
    :else
    (let [^objects a (indexed plan (:universes left))
          ^objects b (indexed plan (:universes right))
          result (scratch a) weight (double weight)
          left-cuts (::tracking-cuts left #{})]
      (doseq [channel (::packed plan)]
        (let [av (read-word a channel) bv (read-word b channel)]
          (write-word! result channel (+ av (* weight (- bv av))))))
      ;; For an interior sample, use the rejected endpoint's actual bytes.
      ;; This also handles inverted, held and cross-universe emission lanes.
      (when-let [right-cuts (::tracking-cuts right)]
        (copy-tracking-emission! plan b result (remove left-cuts right-cuts)))
      (when (seq left-cuts)
        (copy-tracking-emission! plan a result left-cuts))
      (immutable plan result))))

(defn- fade [plan universes gain]
  (if (>= gain 1) universes
      (let [^objects source (indexed plan universes) result (scratch source) gain (double gain)]
        (doseq [^PackedChannel channel (::packed plan) :when (.-fade channel)]
          (write-word! result channel (* gain (read-word source channel))))
        (immutable plan result))))

(defn present
  "Sample the presentation timeline without advancing effects.

  Returns {:state ... :packet packet-or-nil}. :time-ms/:frame-id on a packet
  identify its lower source frame, not the present wall time. :presentation
  records target/presentation time, both source timestamps, interpolation weight
  and fallback gain. Discrete bytes hold the lower sample until the upper sample
  is due. Between endpoints, tracking cuts hold the follower's emission bytes
  at the rejected sample. Before a buffered stream's first sample is due, packet is nil.
  A backwards physical clock throws; callers must create a new policy for a new
  epoch/clock domain. Repeated calls at the same timestamp are deterministic."
  [state now-ms]
  (when-not (and (nonnegative? now-ms)
                 (or (nil? (:last-presented-at-ms state)) (<= (:last-presented-at-ms state) now-ms)))
    (fail! "Presentation time must be finite and monotonic" {:time-ms now-ms}))
  (let [{:keys [mode period-ms latency-ms fade-ms]} (:options state)
        target (- now-ms (if (= mode :buffered-interpolation) latency-ms 0))
        available (filterv #(<= (:completed-at-ms %) now-ms) (:history state))
        left (last (filter #(<= (:time-ms %) target) available))
        right (when (and left (= mode :buffered-interpolation))
                (first (filter #(> (:time-ms %) target) available)))
        weight (if right (/ (- target (:time-ms left)) (- (:time-ms right) (:time-ms left))) 0.0)
        gain (if (or (nil? left) right (= mode :direct)) 1.0
                 (unit (- 1.0 (/ (max 0.0 (- target (:time-ms left) period-ms)) fade-ms))))
        bytes (when left (fade (:plan state)
                               (if right (interpolate (:plan state) left right weight) (:universes left)) gain))]
    {:state (assoc state :last-presented-at-ms now-ms)
     :packet (when left
               (assoc (dissoc left ::tracking-cuts) :universes bytes
                      :presentation {:mode mode :presented-at-ms now-ms :target-time-ms target
                                     :source-times [(:time-ms left) (when right (:time-ms right))]
                                     :weight weight :gain gain :fallback? (and (not= mode :direct) (nil? right)
                                                                              (> target (+ (:time-ms left) period-ms)))}))}))

(ns afterglow.render.atmosphere
  "Venue fog mass balance from the DMX levels actually presented. Volumes are
  equivalent cubic metres at the fogger's manufacturer-rated output density.")

(defn- finite? [x] (and (number? x) (Double/isFinite (double x))))
(defn- xyz? [v] (and (vector? v) (= 3 (count v)) (every? finite? v)))
(defn- require! [ok message data] (when-not ok (throw (ex-info message data))))
(defn- flow? [x] (and (finite? x) (< 0 x 1e9)))

(defn- physical-bytes [channel physical]
  (if (:fine channel)
    [(int physical) (Math/round (* 255.0 (- (double physical) (int physical))))]
    [(Math/round (double physical))]))

(defn- ticks [[coarse fine]]
  (+ (* 255 coarse) (or fine 0)))

(defn validate-fogger! [{:keys [id channels fogger]}]
  (let [{:keys [flow-m3-min direction mixing-seconds dmx-range]
         :or {mixing-seconds 8 direction [0 0 1] dmx-range [0 255]}} fogger]
    (require! (and (map? fogger) (:fog channels) (flow? flow-m3-min)
                   (finite? mixing-seconds) (<= 0.001 mixing-seconds 86400)
                   (xyz? direction) (some #(not (zero? %)) direction)
                   (vector? dmx-range) (= 2 (count dmx-range))
                   (every? #(and (finite? %) (<= 0 % 255)) dmx-range)
                   (not (== (first dmx-range) (second dmx-range))))
              "Fogger needs a fog channel, positive rated m³/min, mixing time, nozzle direction and distinct DMX endpoints"
              {:fixture-id id :fogger fogger})
    (let [raw (:fog channels)
          width {:fine (if (vector? raw) (second raw) (:fine-offset raw))}
          endpoint-ticks (map #(ticks (physical-bytes width %)) dmx-range)]
      (require! (apply not= endpoint-ticks) "Fog endpoints must resolve to distinct deliverable DMX levels"
                {:fixture-id id :dmx-range dmx-range}))))

(defn off-bytes
  "Unsigned physical off bytes keyed by [universe zero-based-offset] for a compiled fixture."
  [{:keys [fogger compiled-channels]}]
  (if fogger
    (let [channel (:fog compiled-channels)
          off (first (:dmx-range fogger [0 255]))]
      (zipmap (remove nil? [(:coarse channel) (:fine channel)]) (physical-bytes channel off)))
    {}))

(defn physical-level
  "Convert a desired physical coarse-unit DMX value to a normalized effect input.
  Inversion reflects the interval from its pivot upwards. On fractional pivots,
  choose the representable level that reproduces the requested coarse/fine bytes."
  [{:keys [inverted-from] :as channel} physical]
  (require! (and (finite? physical) (<= 0 physical 255)) "Physical fog level must be in [0,255]" {:value physical})
  (let [pivot (some-> inverted-from double)
        inverted? (and pivot (>= (double physical) pivot))
        level (/ (if inverted? (+ pivot (- 255.0 (double physical))) (double physical)) 255.0)
        target (physical-bytes channel physical)
        matches? (fn [v]
                   (let [raw (* 255.0 v)
                         out (if (and pivot (>= raw pivot)) (- 255.0 (- raw pivot)) raw)]
                     (and (<= 0.0 v 1.0) (= target (physical-bytes channel out)))))]
    (or (some #(when (matches? %) %) [level (Math/nextDown level) (Math/nextUp level)]) level)))

(defn plan
  "Compile the fog-capable part of a patch. Pass the room in metres and a
  frame/compile-patch result. DMX range is [off full] in physical byte units."
  [room patch]
  (let [{:keys [width height depth air-changes-per-hour fog-half-life-s measured-fog]
         :or {width 12 height 5 depth 10 air-changes-per-hour 0 fog-half-life-s 180}} room
        volume (* (double width) (double height) (double depth))
        {:keys [clearance-half-life-s extinction-per-m reference-path-m]
         :or {extinction-per-m 1.25 reference-path-m 1.0}} measured-fog]
    (require! (and (every? #(and (finite? %) (pos? %)) [width height depth volume fog-half-life-s])
                   (finite? air-changes-per-hour) (<= 0 air-changes-per-hour 3600))
              "Invalid fog room dimensions, ventilation or decay time" {:room room})
    (require! (and (or (nil? measured-fog)
                       (and (map? measured-fog) (finite? clearance-half-life-s) (<= 0.1 clearance-half-life-s 86400)))
                   (finite? extinction-per-m) (<= 0.001 extinction-per-m 1000)
                   (finite? reference-path-m) (<= 0.1 reference-path-m 1000))
              "Invalid measured fog clearance, extinction or sightline length" {:measured-fog measured-fog})
    {:volume-m3 volume :extinction-per-m extinction-per-m :reference-path-m reference-path-m
     :loss-per-s (if clearance-half-life-s (/ (Math/log 2) clearance-half-life-s)
                     (+ (/ air-changes-per-hour 3600.0) (/ (Math/log 2) fog-half-life-s)))
     :sources
     (mapv (fn [{:keys [id position fogger compiled-channels] :as fixture}]
             (validate-fogger! fixture)
             (let [v (:direction fogger [0 0 1])
                   channel (:fog compiled-channels)
                   endpoints (mapv #(physical-bytes channel %) (:dmx-range fogger [0 255]))
                   length (Math/hypot (Math/hypot (double (first v)) (double (second v))) (double (nth v 2)))]
               {:fixture-id id :position (or position [0 0 0]) :direction (mapv #(/ % length) v)
                :max-flow-m3-s (/ (:flow-m3-min fogger) 60.0)
                :mix-per-s (/ 1.0 (:mixing-seconds fogger 8.0))
                :dmx-range (:dmx-range fogger [0 255]) :channel channel
                :off-bytes (first endpoints) :endpoint-ticks (mapv ticks endpoints)}))
           (filter :fogger (:fixtures patch)))}))

(defn- source-state [spec]
  (merge (select-keys spec [:fixture-id :position :direction])
         {:flow-m3-s 0.0 :emitted-m3 0.0 :local-m3 0.0}))

(defn- mixed-state [state plan volume]
  (let [density (/ volume (:volume-m3 plan))]
    (assoc state :mixed-m3 volume :mixed-density density
           :fog-level (- (Math/expm1 (- (* density (:extinction-per-m plan) (:reference-path-m plan))))))))

(defn initial [plan epoch now]
  (require! (finite? now) "Expected a finite monotonic sample time" {:time now})
  (mixed-state (merge (select-keys plan [:volume-m3 :extinction-per-m :reference-path-m])
                      {:epoch epoch :sample-time-ms now :sources (mapv source-state (:sources plan))})
               plan 0.0))

(defn held-volume
  "Equivalent fog volume after a held flow (m³/s) and a positive loss rate (/s)."
  ^double [^double volume ^double flow ^double decay ^double seconds]
  ;; Exact solution for a held pump level and first-order losses. expm1
  ;; preserves mass for very short output intervals.
  (let [x (- (* decay seconds))]
    (+ (* volume (Math/exp x)) (* flow (/ (- (Math/expm1 x)) decay)))))

(defn advance
  "Integrate the previously presented flows up to now in monotonic milliseconds.
  A stopped pump continues to diffuse and clear even at a stopped musical clock."
  [plan state now]
  (require! (and (finite? now) (>= now (:sample-time-ms state))) "Fog clock went backwards" {:now now})
  (if (== now (:sample-time-ms state)) state
    (let [seconds (/ (- now (:sample-time-ms state)) 1000.0)
          loss (:loss-per-s plan)
          sources (:sources state)
          total (reduce + (:mixed-m3 state) (map :local-m3 sources))
          flow (reduce + 0.0 (map :flow-m3-s sources))
          remaining (held-volume total flow loss seconds)
          next-sources (mapv (fn [source spec]
                               (let [rate (:flow-m3-s source)]
                                 (-> source
                                     (assoc :local-m3 (held-volume (:local-m3 source) rate (+ loss (:mix-per-s spec)) seconds))
                                     (update :emitted-m3 + (* rate seconds)))))
                             sources (:sources plan))
          mixed (max 0.0 (- remaining (reduce + 0.0 (map :local-m3 next-sources))))]
      (mixed-state (assoc state :sample-time-ms now :sources next-sources) plan mixed))))

(defn reconfigure
  "Keep existing fog on a rig change. Retired jets join the mixed room. Call
  advance with the previous plan first. Set resume? on restore to stop pumps
  and rebase the saved quantities to the new monotonic clock."
  [plan state epoch now resume?]
  (let [old (into {} (map (juxt :fixture-id identity)) (:sources state))
        blank (initial plan epoch now)
        sources (mapv (fn [s]
                        (let [saved (get old (:fixture-id s))]
                          (cond-> (merge s (select-keys saved [:emitted-m3 :local-m3 :flow-m3-s]))
                            (not resume?) (merge (select-keys saved [:dmx-coarse :dmx-fine]))
                            resume? (assoc :flow-m3-s 0.0)))) (:sources blank))
        retired (apply dissoc old (map :fixture-id sources))
        mixed (reduce + (double (:mixed-m3 state 0)) (map :local-m3 (vals retired)))]
    (mixed-state (assoc blank :sources sources) plan mixed)))

(defn- dmx-byte [universes [u i]]
  (when-let [data (get universes u)]
    (when (< i (count data)) (bit-and 255 (int (nth data i))))))

(defn present
  "Advance the previous interval, then latch newly delivered coarse/fine DMX.
  A universe absent from a partial update retains its last received level."
  [plan state now universes]
  (let [updated (update (advance plan state now) :sources
          (fn [sources]
            (mapv (fn [s {:keys [channel off-bytes endpoint-ticks max-flow-m3-s]}]
                    (let [{:keys [coarse fine]} channel
                          received-hi (dmx-byte universes coarse)
                          received-lo (when fine (dmx-byte universes fine))]
                      (if (or (some? received-hi) (some? received-lo))
                        (let [[off full] endpoint-ticks
                              hi (or received-hi (:dmx-coarse s) (first off-bytes))
                              lo (if fine (or received-lo (:dmx-fine s) (second off-bytes)) 0)
                              amount (min 1.0 (max 0.0 (/ (double (- (+ (* 255 hi) lo) off)) (- full off))))]
                          (assoc s :flow-m3-s (* amount max-flow-m3-s) :dmx-coarse hi :dmx-fine lo
                                 :last-presented-ms now))
                        s))) sources (:sources plan))))]
    (cond-> updated (some #(= now (:last-presented-ms %)) (:sources updated))
      (assoc :last-presented-ms now))))

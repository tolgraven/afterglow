(ns afterglow.spatial
  "Advance a venue's selection volumes from an explicit clock, patch and observed
  HDR field. Transport, cue ownership and running user callbacks belong to the host."
  (:require [afterglow.spatial.geometry :as geometry]
            [afterglow.spatial.motion :as motion]
            [afterglow.spatial.trace :as trace]
            [afterglow.time :as time]
            [clojure.set :as set]))

(def default-bounds {:min [-5.0 0.0 -5.0] :max [5.0 5.0 5.0]})
(def default-gravity [0.0 -9.81 0.0])

(defn validate! [config]
  (let [{:keys [bounds gravity volumes] :or {bounds default-bounds gravity default-gravity volumes {}}} config]
    (when-not (and (map? config) (geometry/box? bounds) (geometry/vec3? gravity)
                   (map? volumes) (<= (count volumes) 256)
                   (<= (count (filter #(= :ball (:shape %)) (vals volumes))) 64))
      (geometry/invalid! "Spatial configuration needs a room, a gravity vector and bounded volumes" config))
    (doseq [[id {:keys [shape source-id threshold] :as volume}] volumes]
      (when-not (geometry/valid-id? id) (geometry/invalid! "Spatial volume ID needs a keyword or string" id))
      (if (= shape :hdr)
        (when-not (and (or (nil? source-id) (geometry/valid-id? source-id))
                       (or (nil? threshold) (geometry/nonnegative? threshold)))
          (geometry/invalid! "HDR volume source or threshold is invalid" volume))
        (geometry/validate! volume))
      (when (= shape :ball) (motion/validate! {:bounds bounds} volume)))
    config))

(defrecord Scene [bounds gravity volumes order balls traces])

(defn prepare
  "Validate resolved settings and establish permanent ordering for a configuration.
  Cache the result beside the prepared patch when advancing a running show."
  [config]
  (if (instance? Scene config) config
    (let [{:keys [bounds gravity volumes] :or {bounds default-bounds gravity default-gravity volumes {}}} (validate! config)
          order (vec (sort-by pr-str (keys volumes)))]
      (let [balls (filterv #(= :ball (:shape (volumes %))) order)
            traces (into {} (keep (fn [id]
                                    (when-let [geometry (get-in volumes [id :geometry])]
                                      [id (trace/prepare geometry)]))) balls)]
        (->Scene bounds gravity volumes order balls traces)))))

(defn prepare-rig [fixtures] (geometry/prepare-rig fixtures))

(defn- hdr-members [rig source-id threshold contacts]
  (into #{} (comp (mapcat seq) (keep (fn [[id peak]]
                                       (when (and (contains? (:ids rig) id) (> peak threshold)) id))))
        (if source-id [(get contacts source-id)] (vals contacts))))

(defn- members [rig volume body contacts]
  (if (= :hdr (:shape volume))
    (hdr-members rig (:source-id volume) (:threshold volume 0.0) contacts)
    (geometry/fixtures-in rig (cond-> volume body (assoc :position (:position body))))))

(defn- transitions [id previous current now]
  (into [] (mapcat (fn [[event-type ids]]
                     (map (fn [fixture-id] {:type event-type :volume-id id :fixture-id fixture-id :time-ms now})
                          (sort-by pr-str ids))))
        [[:spatial/exit (set/difference previous current)]
         [:spatial/enter (set/difference current previous)]]))

(defn- observe [state ids specs rig hdr now]
  (reduce (fn [out id]
            (let [before (get-in out [:members id] #{})
                  after (members rig (specs id) (get-in out [:bodies id]) hdr)]
              (cond-> (assoc-in out [:members id] after)
                (not= before after) (update :events into (transitions id before after now)))))
          state ids))

(defn- observe-segment [state id sweep start finish p0 p1]
  (if (every? true? (map == p0 p1)) state
    (let [was (get-in state [:members id] #{})
          hits (sweep p0 p1)
          event (fn [type fixture t]
                  {:type type :volume-id id :fixture-id fixture :time-ms (+ start (* (- finish start) t))})
          leaving (set/difference was (into #{} (map first) hits))
          follow (fn [[inside events] [fixture entry exit stays?]]
                   [(if stays? (conj inside fixture) (disj inside fixture))
                    (cond-> events
                      (not (inside fixture)) (conj (event :spatial/enter fixture entry))
                      (not stays?) (conj (event :spatial/exit fixture exit)))])
          [inside events] (reduce follow [(set/difference was leaving) (:events state)] hits)]
      (-> state (assoc-in [:members id] inside)
          (assoc :events (into events (map #(event :spatial/exit % 0.0)) (sort-by pr-str leaving)))))))

(defn- volume-sweep [rig {:keys [radius translation]} trace]
  (let [sweep (if trace (partial geometry/sweep-geometry rig trace)
                  (fn [from to] (geometry/sweep rig from to radius)))]
    (if translation
      (fn [from to] (sweep (mapv + from translation) (mapv + to translation)))
      sweep)))

(defn- observe-motion [out before ids volumes traces rig start wall-paths]
  (reduce
    (fn [state id]
      (let [p0 (get-in before [:bodies id :position]) p1 (get-in state [:bodies id :position])
            sweep (volume-sweep rig (volumes id) (traces id)) end (+ start motion/step-ms)]
        (if-let [waypoints (get wall-paths id)]
          (loop [state state t0 start p0 p0 remaining (seq waypoints)]
            (if-let [[offset p] (first remaining)]
              (let [t (+ start offset)]
                (recur (observe-segment state id sweep t0 t p0 p) t p (next remaining)))
              (observe-segment state id sweep t0 end p0 p1)))
          (observe-segment state id sweep start end p0 p1))))
    out ids))

(defn- signals [{:keys [shape position radius min max]} body]
  (cond
    body
    (let [velocity (:velocity body)
          speed (geometry/length3 velocity)]
      (assoc (select-keys body [:position :velocity :rotation :deformation])
             :radius radius :speed speed
             :direction (if (zero? speed) motion/zero3 (mapv #(/ % speed) velocity))))
    position (cond-> {:position position} radius (assoc :radius radius))
    (= :box shape) {:position (mapv #(/ (+ %1 %2) 2.0) min max)}
    :else {}))

(defn rebase
  "Keep position, contacts and membership when resuming a sleeping stream or
  restoring a show in a new epoch. Exclude time the simulation did not own."
  [state clock]
  (when state
    (when-not (time/finite-number? (:time-ms clock)) (geometry/invalid! "Spatial clock needs finite milliseconds" clock))
    (assoc state :time-ms (:time-ms clock) :epoch (:epoch clock) :playing? (not= false (:playing? clock)))))

(defn advance
  "Advance up to 400 ms in fixed 5 ms steps. Long stalls discard older catch-up
  time and expose :dropped-ms. Pausing freezes physical time; edited selections
  and fixture removals still take effect. Inputs can be ordinary maps and fixture
  vectors or prepared with prepare/prepare-rig. Pass the returned :state at the
  next frame. Its data and the signal/event outputs can all be saved as Transit."
  [previous config clock fixtures hdr-contacts]
  (let [{:keys [balls volumes order bounds] :as scene} (prepare config)
        now (:time-ms clock) playing? (not= false (:playing? clock))
        _ (when-not (time/finite-number? now) (geometry/invalid! "Spatial clock needs finite milliseconds" clock))
        before (:time-ms previous now)
        prior (when (and (= (:epoch clock) (:epoch previous)) (<= before now)) previous)
        elapsed (if (and prior playing? (:playing? prior)) (- now before) 0.0)
        available (+ (:remainder-ms prior 0.0) elapsed)
        steps (if (seq balls) (min motion/max-steps (long (/ available motion/step-ms))) 0)
        remainder (if (seq balls) (mod available motion/step-ms) 0.0)
        period (* steps motion/step-ms)
        dropped (if (seq balls) (max 0 (- available period remainder)) 0.0)
        start (- now period remainder)
        rig (when (seq order) (prepare-rig fixtures))
        bodies (into {} (for [id balls] [id (motion/body (get-in prior [:bodies id]) bounds (volumes id))]))
        old-members (:members prior {})
        removed (remove (set order) (sort-by pr-str (keys old-members)))
        exits (if (and previous (nil? prior))
                (into [] (mapcat #(transitions % (get-in previous [:members %]) #{} now))
                      (sort-by pr-str (keys (:members previous))))
                (into [] (mapcat #(transitions % (old-members %) #{} now)) removed))
        initial (observe {:bodies bodies :contacts (:contacts prior #{}) :members (select-keys old-members order) :events exits}
                         order volumes rig hdr-contacts (if (pos? steps) start now))
        final (reduce (fn [current i]
                        (let [t (+ start (* i motion/step-ms))
                              next (motion/step (:bodies current) (:contacts current) balls volumes scene t)]
                          (observe-motion (-> current (assoc :bodies (:bodies next) :contacts (:contacts next))
                                              (update :events into (:events next)))
                                          current balls volumes (:traces scene) rig t (:wall-paths next))))
                      initial (range steps))
        state (assoc (dissoc final :events) :epoch (:epoch clock) :time-ms now :playing? playing? :remainder-ms remainder)]
    {:state state :members (:members final) :dropped-ms dropped
     :signals (into {} (for [id order] [id (signals (volumes id) (get-in final [:bodies id]))]))
     :events (vec (sort-by :time-ms (:events final)))}))

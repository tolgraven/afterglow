(ns afterglow.render.emission
  "Read and adjust light at the output of a composed frame. Levels include the
  operator master. Non-emission channels retain their packed values."
  (:require [afterglow.render.dmx :as dmx]
            [afterglow.render.emission.dense :as dense]
            [afterglow.render.frame :as frame]
            [afterglow.render.photometry :as photometry]))

(defn- read-byte-at [universes [u slot]]
  (bit-and 255 (aget ^bytes (get universes u) (int slot))))

(defn- drive ^double [raw pivot]
  (/ (if (and pivot (>= raw pivot)) (+ pivot (- 255.0 raw)) raw) 255.0))

(defn- channel-level [universes {:keys [coarse fine inverted-from] :as channel}]
  (drive (if fine
           (dmx/coarse-units (read-byte-at universes coarse) (read-byte-at universes fine) (::frame/coarse-range? channel))
           (read-byte-at universes coarse))
         inverted-from))

(defn levels
  "Read normalized post-master DMX dimmer and additive channels on a compiled
  fixture. An unmetered utility or movement-only fixture returns nil."
  [fixture frame]
  (when-let [channels (::frame/emission-channels fixture)]
    (update-vals channels #(channel-level (:universes frame) %))))

(defn- emitted [raw]
  (if (and (contains? raw :dimmer) (> (count raw) 1))
    (update-vals (dissoc raw :dimmer) #(* (:dimmer raw) %))
    raw))

(defn emitted-levels
  "Normalized delivered drive of each actual emitter, including any hardware
  dimmer. A fixed lamp has one :dimmer source. An unlit RGB head has zero
  drive on each emitter even if its dimmer is open."
  [fixture frame]
  (emitted (levels fixture frame)))

(defn- unit! [x]
  (when-not (and (number? x) (Double/isFinite (double x)) (<= 0 x 1))
    (throw (ex-info "Expected normalized fixture emission" {:level x})))
  (double x))

(defn- write-channel! [buffers {:keys [coarse fine] :as channel} value down?]
  (let [word (long (dense/packed-word channel (unit! value) down?))
        put! (fn [[u slot] v] (aset-byte ^bytes (get buffers u) (int slot) (unchecked-byte v)))]
    (if fine
      (do (put! coarse (unsigned-bit-shift-right word 8)) (put! fine (bit-and word 255)))
      (put! coarse word))))

(defn- display-values [fixture raw]
  (let [colors (dissoc raw :dimmer)
        dimmer (:dimmer raw 1.0)
        tint (if (seq colors)
               (reduce-kv (fn [rgb attr level]
                            (mapv (fn [c t] (+ c (* level t))) rgb (second (photometry/emitter-spectrum attr))))
                          [0.0 0.0 0.0] colors)
               (:emission-color fixture [1.0 1.0 1.0]))]
    {:emitted-color (mapv #(* dimmer (min 1.0 %)) tint)
     :intensity (:dimmer raw (reduce max 0.0 (vals colors)))}))

(defn- copy-projections [frame]
  (cond-> (update frame :universes update-vals #(aclone ^bytes %))
    (:compact frame)
    (update-in [:compact :fields] (fn [fields]
                                    (reduce #(update-in %1 [%2 :values] (fn [values] (aclone ^doubles values)))
                                            fields [:emitted-color :intensity])))))

(defn- project [out fixture raw]
  (let [id (:id fixture)
        {:keys [emitted-color intensity] :as display} (display-values fixture raw)]
    (when-let [fields (get-in out [:compact :fields])]
      (let [i (int (::frame/index fixture))
            ^doubles colors (get-in fields [:emitted-color :values])]
        (dotimes [c 3] (aset-double colors (+ (* i 3) c) (double (nth emitted-color c))))
        (aset-double ^doubles (get-in fields [:intensity :values]) i (double intensity))))
    (cond-> out
      (:values out)
      (update-in [:values id] (fn [v] (-> v (merge display)
                                          (update :channels merge raw)
                                          (assoc :emitter-values (dissoc raw :dimmer))))))))

(defn- rewrite [patch frame targets transform down?]
  (if (empty? targets) frame
    (reduce-kv
     (fn [out id target]
       (let [fixture (get-in patch [:by-id id])
             channels (::frame/emission-channels fixture)
             raw (when channels (levels fixture frame))
             changes (when channels (transform raw target))]
         (if (empty? changes) out
           (let [out (if (identical? out frame) (copy-projections frame) out)]
             (run! (fn [[attr x]]
                     (write-channel! (:universes out) (get channels attr) x down?)) changes)
             (project out fixture (levels fixture out))))))
     frame targets)))

(defn- rich-output [patch {:keys [frame ^booleans changed]}]
  (if-not changed frame
    (reduce (fn [out i]
              (if (aget changed i)
                (let [fixture (nth (:fixtures patch) i)]
                  (project out fixture (levels fixture out)))
                out)) frame (range (alength changed)))))

(defn scale-emission
  "Apply fixture ID -> gain in [0,1] to one completed frame. Alternatively
  supply a double-array of gains in patch target order. Attenuates a physical
  dimmer once, otherwise each emitter, rounding toward lower delivered drive."
  [patch frame gains]
  (rich-output patch (dense/scale (::frame/emission-layout patch) frame gains copy-projections)))

(defn follow-frame
  "Follow actual post-master light with asymmetric response coefficients.
  A coefficient of one is immediate. Supply a scalar across the rig or a
  double-array in fixture order per stage, with negative entries for bypass.
  Include a prior frame from the same rig to initialize a new response;
  thereafter pass the returned private :levels as immutable input. Hard
  blackout and transport overrides are enforced by the caller. Optionally pass
  {:attack boolean-or-boolean-array :release boolean-or-boolean-array
   :previous last-ramps}. Flagged coefficients then represent a fraction of a
  finite linear transition duration consumed this tick. Each emitter tracks
  its own target, preserving continuity when only one color channel changes."
  ([patch frame previous prior-frame attack release ceiling]
   (follow-frame patch frame previous prior-frame attack release ceiling nil))
  ([patch frame previous prior-frame attack release ceiling ramps]
   (let [result (dense/follow (::frame/emission-layout patch) frame previous prior-frame
                              attack release ceiling copy-projections ramps)]
     (assoc (select-keys result [:levels :ramps]) :frame (rich-output patch result)))))

(defn with-emitted-levels
  "Replace delivered per-emitter drive for selected fixtures using the same
  shape as emitted-levels. For heads with a physical dimmer, retain its level
  whenever it can reproduce the requested color, raising it only as needed.
  Caller supplies the desired post-master values; hard blackout and operator
  overrides belong to the show. Original buffers remain immutable."
  [patch frame targets]
  (rewrite patch frame targets
           (fn [raw target]
             (let [desired (update-vals target unit!)
                   previous (emitted raw)]
               (when-not (= (set (keys desired)) (set (keys previous)))
                 (throw (ex-info "Emitted levels must specify the fixture's actual emitters" {:target target})))
               (when (not= desired previous)
                 (if (and (contains? raw :dimmer) (> (count raw) 1))
                   (let [d (reduce max (:dimmer raw) (vals desired))]
                     (if (zero? d) {:dimmer 0.0}
                       (assoc (update-vals desired #(/ % d)) :dimmer d)))
                   desired))))
           false))

(defn falling-heads
  "Boolean array, in patch target order, identifying a fall in at least one
  emitted component between two frames. Both frames must use the same patch."
  [patch previous frame]
  (dense/falling-heads (::frame/emission-layout patch) previous frame))

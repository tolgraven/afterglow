(ns afterglow.spatial.field
  "Pure, weighted venue masks for native light and cue contributions."
  (:require [afterglow.render.frame :as frame]
            [afterglow.spatial.geometry :as geometry]
            [afterglow.spatial.beam :as beam]
            [afterglow.spatial.shape :as shape]
            [afterglow.time :as time]
            [clojure.set :as set])
  (:import [clojure.lang IFn$DD]))

(defn- fade [curve x]
  (case curve :linear x :smoothstep (* x x (- 3.0 (* 2.0 x)))))

(defn- floating-falloff
  "Compile the signed-distance response of a sphere with floating-point widths."
  [strength inner outer curve]
  (let [strength (double strength)
        full-through (- (double inner))
        empty-from (double outer)
        width (+ (double inner) empty-from)
        smooth? (= curve :smoothstep)]
    (fn ^double [^double distance]
      (cond
        (<= distance full-through) strength
        (>= distance empty-from) 0.0
        :else (let [x (/ (- empty-from distance) width)]
                (* strength (if smooth? (* x x (- 3.0 (* 2.0 x))) x)))))))

(defn- sphere-point-weight [[cx cy cz] radius ^IFn$DD falloff]
  (let [cx (double cx) cy (double cy) cz (double cz) radius (double radius)]
    (fn [[x y z]]
      (let [xy (Math/hypot (- (double x) cx) (- (double y) cy))]
        (.invokePrim falloff (- (Math/hypot xy (- (double z) cz)) radius))))))

(defn- radial-radius [{:keys [shape scale geometry radius]}]
  (when (and (#{:sphere :ball} shape) (nil? geometry) (or (nil? scale) (apply == scale)))
    (* radius (get scale 0 1.0))))

(defn- weight-response [radius strength inner outer curve]
  (if (and radius (pos? strength) (double? radius) (double? inner) (double? outer))
    (floating-falloff strength inner outer curve)
    (let [width (+ inner outer)]
      (fn [distance]
        (* (double strength)
           (cond (<= distance (- inner)) 1.0
                 (>= distance outer) 0.0
                 :else (fade curve (/ (- outer distance) width))))))))

(defn- radial-sampler [radius center outer response]
  (when radius
    {:center center :support (+ radius outer)
     :by-distance (if (instance? IFn$DD response)
                    (let [r (double radius)]
                      (fn ^double [^double distance] (.invokePrim ^IFn$DD response (- distance r))))
                    (fn [distance] (response (- distance radius))))}))

(defn- point-sampler [{:keys [position scale translation]} {:keys [inside? distance]}
                      response radius width strength]
  (let [floating? (instance? IFn$DD response)]
    (cond
      (and floating? (nil? translation) (nil? scale) (every? double? position))
      (sphere-point-weight position radius response)
      (zero? width) (fn [point] (if (inside? point) (double strength) 0.0))
      floating? (fn [point] (.invokePrim ^IFn$DD response (double (distance point))))
      :else (comp response distance))))

(defn prepare
  "Compile resolved metres, strength and blending settings once per shape edit.
  The inner and outer widths specify where a full-strength core starts fading
  and where spill reaches zero. Without a falloff the surface is inclusive."
  [{:keys [strength falloff selection] :or {strength 1.0 selection #{:position}} :as volume}]
  (geometry/validate! volume)
  (let [{:keys [inner-m outer-m curve] :or {inner-m 0.0 outer-m 0.0 curve :linear}} falloff
        width (when (and (geometry/nonnegative? inner-m) (geometry/nonnegative? outer-m))
                (+ inner-m outer-m))]
    (when-not (and (or (nil? falloff) (map? falloff)) (time/finite-number? strength) (<= 0 strength 1)
                   (time/finite-number? width) (#{:linear :smoothstep} curve)
                   (set? selection) (set/subset? selection #{:position :beam :aimable}))
      (geometry/invalid! "Invalid volume strength, falloff or selection" volume))
    (let [{:keys [bounds witnesses falloff-stretch] :or {falloff-stretch [1.0 1.0 1.0]} :as shape}
          (shape/prepare volume)
          center (shape/center bounds)
          radius (radial-radius volume)
          response (weight-response radius strength inner-m outer-m curve)
          expand (fn [corner sign] (mapv #(+ (double %1) (* sign outer-m %2)) corner falloff-stretch))]
      {:bounds (when bounds {:min (expand (:min bounds) -1) :max (expand (:max bounds) 1)})
       :center center :witnesses witnesses :selection selection :max-weight (double strength)
       :radial (radial-sampler radius center outer-m response)
       :weight-at (point-sampler volume shape response radius width strength)})))

(defn- position-weights [{:keys [weight-at bounds selection]} rig]
  (if-not (contains? selection :position) {}
    (let [[_ ymin zmin] (:min bounds)
          [_ ymax zmax] (:max bounds)
          collect (fn [weights [id [_ y z :as p]]]
                    (if (and bounds (or (< y ymin) (> y ymax) (< z zmin) (> z zmax)))
                      weights
                      (let [w (weight-at p)] (if (pos? w) (assoc! weights id w) weights))))]
      (persistent! (reduce collect (transient {}) (geometry/candidates rig bounds))))))

(defn positions
  "Sample the emitting positions of the given patch. Return weights by head ID."
  [volume fixtures]
  {:weights (position-weights (prepare volume) (geometry/prepare-rig fixtures)) :aims {}})

(defn prepare-observations
  "Prepare receiver planes and optical settings outside the per-volume loop.
  Attach the committed :values map or id-to-row function when sampling."
  [options]
  (assoc options ::optics (beam/prepare-options (assoc options :selection #{}))))

(defn compact-observations
  "Attach a completed compact frame and its matching target index to optical
  settings. A sampler shares the emission read across volumes in this frame."
  [options index compact]
  (let [attributes [:emitted-color :pan :tilt :zoom :direction :shutter :strobe]
        read-row (frame/compact-reader index compact attributes)]
    (assoc options :values (with-meta read-row {::observe (beam/compact-observer compact (:indices index) read-row)}))))

(defn- range-origins [emitters]
  (when (seq emitters)
    (reduce (fn [{lo :min hi :max} {:keys [position lens-radius-m]
                                  :or {position [0 0 0] lens-radius-m 0.119}}]
              ;; Read only standard numbers here. A suspect hint disables the
              ;; certificate so the usual fixture selection decides when to validate it.
              (if (and (or (float? lens-radius-m) (integer? lens-radius-m)
                           (decimal? lens-radius-m) (ratio? lens-radius-m))
                       (geometry/nonnegative? lens-radius-m) (geometry/vec3? position))
                {:min (mapv #(min %1 (double %2)) lo position)
                 :max (mapv #(max %1 (double %2)) hi position)}
                (reduced nil)))
            {:min [##Inf ##Inf ##Inf] :max [##-Inf ##-Inf ##-Inf]}
            emitters)))

(defn prepare-rig
  "Build spatial indices now and prepare optical fixtures on first beam use."
  [fixtures]
  (let [rig (geometry/prepare-rig fixtures)]
    (if (::optical-rig rig) rig
        (assoc rig ::optical-rig (delay (let [fixtures (mapv beam/prepare-fixture (:directional rig))]
                                           {:fixtures fixtures :origins (range-origins fixtures)}))))))

(defn- sample-volume [volume rig {:keys [values] :as observations} emissions]
  (let [sampling (prepare volume)
        initial (position-weights sampling rig)
        optical (disj (:selection sampling) :position)]
    (if (empty? optical)
      {:weights initial :aims {}}
      (let [prepared (or (::optics observations) (::optics (prepare-observations observations)))
            {:keys [fixtures origins]} @(::optical-rig rig)
            opts (beam/volume-options prepared optical sampling origins)
            read-row (or values {})
            receive (if emissions
                      #(beam/observed-contribution % volume sampling opts)
                      #(beam/contribution % (read-row (:id %)) volume sampling opts))
            aims (volatile! (transient {}))
            add-beam (fn [weights source]
                       (if-let [{:keys [weight aim]} (receive source)]
                         (let [id (:id source)]
                           (when aim (vswap! aims assoc! id aim))
                           (assoc! weights id (max weight (get weights id 0.0))))
                         weights))]
        {:weights (persistent! (reduce add-beam (transient initial) (if emissions @emissions fixtures)))
         :aims (persistent! @aims)}))))

(defn sample
  "Sample the volume against a prepared patch and its last committed emitter
  values. Overlapping position and optical matches use the largest weight.
  :aims contains reachable world-space targets when :aimable was requested."
  [volume fixtures observations]
  (sample-volume volume (prepare-rig fixtures) observations nil))

(defn sampler
  "Create a sampler for several volumes against one immutable frame. Optical
  queries share the committed light level and pose for each head. Position-only
  queries do not read emission data. Discard the sampler on a new frame or patch."
  [fixtures {:keys [values] :as observations}]
  (let [rig (prepare-rig fixtures)
        read-row (or values {})
        observe (or (::observe (meta read-row)) #(beam/observe % (read-row (:id %))))
        emissions (delay (mapv observe (:fixtures @(::optical-rig rig))))]
    (fn [volume] (sample-volume volume rig observations emissions))))

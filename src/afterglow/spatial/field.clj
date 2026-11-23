(ns afterglow.spatial.field
  "Pure, weighted venue masks for native light and cue contributions."
  (:require [afterglow.spatial.geometry :as geometry]
            [afterglow.spatial.beam :as beam]
            [afterglow.spatial.shape :as shape]
            [afterglow.time :as time]
            [clojure.set :as set]))

(defn- fade [curve x]
  (case curve :linear x :smoothstep (* x x (- 3.0 (* 2.0 x)))))

(defn prepare
  "Compile resolved metres, strength and blending settings once per shape edit.
  The inner and outer widths specify where a full-strength core starts fading
  and where spill reaches zero. Without a falloff the surface is inclusive."
  [{:keys [strength falloff selection] :or {strength 1.0 selection #{:position}} :as volume}]
  (geometry/validate! volume)
  (let [{:keys [inner-m outer-m curve] :or {inner-m 0.0 outer-m 0.0 curve :linear}} falloff]
    (when-not (and (or (nil? falloff) (map? falloff)) (time/finite-number? strength) (<= 0 strength 1)
                   (geometry/nonnegative? inner-m) (geometry/nonnegative? outer-m)
                   (time/finite-number? (+ inner-m outer-m)) (#{:linear :smoothstep} curve)
                   (set? selection) (set/subset? selection #{:position :beam :aimable}))
      (geometry/invalid! "Invalid volume strength, falloff or selection" volume))
    (let [{:keys [distance bounds inside? witnesses falloff-stretch] :or {falloff-stretch [1.0 1.0 1.0]}} (shape/prepare volume)
          width (+ inner-m outer-m)
          edge (fn [d] (cond (<= d (- inner-m)) 1.0 (>= d outer-m) 0.0
                             :else (fade curve (/ (- outer-m d) width))))
          radial? (and (#{:sphere :ball} (:shape volume)) (nil? (:geometry volume))
                       (or (nil? (:scale volume)) (apply == (:scale volume))))
          radius (* (or (:radius volume) 0.0) (get (:scale volume) 0 1.0))
          expand (fn [corner sign] (mapv #(+ (double %1) (* sign outer-m %2)) corner falloff-stretch))]
      {:bounds (when bounds {:min (expand (:min bounds) -1) :max (expand (:max bounds) 1)})
       :center (shape/center bounds) :witnesses witnesses
        :selection selection :max-weight (double strength)
       :radial (when radial?
                 {:center (shape/center bounds) :support (+ radius outer-m)
                  :by-distance (fn [d] (* (double strength) (edge (- d radius))))})
       :weight-at (if (zero? width)
                    (fn [p] (if (inside? p) (double strength) 0.0))
                    (fn [p] (* (double strength) (edge (distance p)))))})))

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

(defn sample
  "Sample the volume against a prepared patch and its last committed emitter
  values. Overlapping position and optical matches use the largest weight.
  :aims contains reachable world-space targets when :aimable was requested."
  [volume fixtures {:keys [values] :as observations}]
  (let [sampling (prepare volume)
        rig (geometry/prepare-rig fixtures)
        result {:weights (position-weights sampling rig) :aims {}}
        optical (disj (:selection sampling) :position)]
    (if (empty? optical) result
      (let [prepared (or (::optics observations) (::optics (prepare-observations observations)))
            opts (assoc prepared :selection optical)
            read-row (or values {})
            collect (fn [result {:keys [id] :as fixture}]
                      (if-let [{:keys [weight aim]} (beam/contribution fixture (read-row id) volume sampling opts)]
                        (cond-> (update-in result [:weights id] (fnil max 0.0) weight)
                          aim (assoc-in [:aims id] aim))
                        result))]
        (reduce collect result (:directional rig))))))

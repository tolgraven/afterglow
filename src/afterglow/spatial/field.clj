(ns afterglow.spatial.field
  "Pure, weighted venue masks for native light and cue contributions."
  (:require [afterglow.spatial.geometry :as geometry]
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
    (let [{:keys [distance bounds]} (shape/prepare volume)
          width (+ inner-m outer-m)
          edge (fn [d] (cond (<= d (- inner-m)) 1.0 (>= d outer-m) 0.0
                             :else (fade curve (/ (- outer-m d) width))))
          expand (fn [corner sign] (mapv #(+ (double %) (* sign outer-m)) corner))]
      {:bounds (when bounds {:min (expand (:min bounds) -1) :max (expand (:max bounds) 1)})
       :center (when bounds (mapv #(* 0.5 (+ %1 %2)) (:min bounds) (:max bounds)))
       :selection selection :weight-at (fn [p] (* (double strength) (edge (distance p))))})))

(defn- position-weights [{:keys [weight-at bounds selection]} rig]
  (if (contains? selection :position)
    (into {} (keep (fn [[id point]] (let [w (weight-at point)] (when (pos? w) [id w]))))
          (geometry/candidates rig bounds))
    {}))

(defn positions
  "Sample the emitting positions of the given patch. Return weights by head ID."
  [volume fixtures]
  {:weights (position-weights (prepare volume) (geometry/prepare-rig fixtures)) :aims {}})

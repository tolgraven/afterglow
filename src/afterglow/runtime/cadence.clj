(ns afterglow.runtime.cadence
  "Choose the interval between predictive effect samples from completed frame timings."
  (:require [afterglow.time :as time]))

(def defaults
  {:headroom 0.15 :max-stride 8 :min-cost-ms 0.75
   :pressure-frames 3 :recovery-frames 24 :smoothing 0.2})

(defn settings [options]
  (let [{:keys [headroom max-stride min-cost-ms pressure-frames recovery-frames smoothing] :as s}
        (merge defaults options)]
    (when-not (and (map? options) (every? (set (keys defaults)) (keys options))
                   (time/finite-number? headroom) (<= 0 headroom 0.9)
                   (pos-int? max-stride) (<= max-stride 64)
                   (time/finite-number? min-cost-ms) (not (neg? min-cost-ms))
                   (pos-int? pressure-frames) (pos-int? recovery-frames)
                   (time/finite-number? smoothing) (< 0 smoothing 1))
      (throw (ex-info "Invalid adaptive keyframe settings" {:options options})))
    s))

(defn maximum-stride
  "Largest whole-frame automatic interval allowed by an effect at the current
  tempo and meter. An authored interval already at that limit needs no governor."
  [{:keys [interval max-interval]} {:keys [bpm meter]} period-ms global-max]
  (if max-interval
    (let [span-ms #(time/estimate-ms (time/normalize-duration % meter) bpm)
          limit (max 1 (long (min global-max (/ (span-ms max-interval) period-ms))))]
      (if (and interval (<= (* limit period-ms) (span-ms interval))) 1 limit))
    global-max))

(defn observer
  "Create a worker-safe observer for one frame. Costs use monotonic nanoseconds.
  Responses and exceptions pass through unchanged. The host reads :samples only
  after the worker boundary, and discards this observer when the frame ends."
  ([] (observer #(System/nanoTime)))
  ([now]
   (let [samples (atom {})
         measure (fn [id predictive? calculate]
                   (let [start (now)]
                     (try (calculate)
                          (finally
                            (let [cost (/ (max 0 (- (now) start)) 1e6)]
                              (swap! samples update id
                                     (fn [entry]
                                       {:predictive? predictive?
                                        :calls (inc (:calls entry 0))
                                        :total-ms (+ (:total-ms entry 0.0) cost)})))))))]
     {:measure-effect measure :samples samples})))

(defn- smooth [old sample fraction]
  (if (some? old)
    (+ (double old) (* fraction (- (double sample) (double old))))
    (double sample)))

(defn- record-sample [entry {:keys [calls total-ms predictive?]} fraction frame]
  (let [per-call (/ total-ms calls)]
    (-> entry
        (assoc :cost-ms (smooth (:cost-ms entry) per-call fraction)
               :previous-sample-ms (:last-sample-ms entry)
               :last-sample-ms per-call :sampled-at frame
               :predictive? predictive?)
        (update :evaluations (fnil + 0) calls)
        (update :sampled-frames (fnil inc 0)))))

(defn- update-entry [entry version sample {:keys [smoothing min-cost-ms]} frame limit minimum]
  (let [prior (if (and entry (= version (:version entry))) entry
                {:version version :stride 1 :changed-at frame})
        {:keys [previous-sample-ms last-sample-ms predictive?] :as updated}
        (cond-> prior sample (record-sample sample smoothing frame))
        cheap? (and previous-sample-ms (< (max previous-sample-ms last-sample-ms) min-cost-ms))
        bounded (min (:stride updated) limit)
        stride (if (or cheap? (false? predictive?) (< bounded minimum)) 1 bounded)]
    (cond-> (assoc updated :max-stride limit :stride stride)
      (< stride (:stride updated)) (assoc :changed-at frame))))

(defn- slowdown-candidate [entries minimum {:keys [min-cost-ms]}]
  (->> entries
       (keep (fn [[id {:keys [predictive? cost-ms stride max-stride changed-at sampled-at previous-sample-ms last-sample-ms]}]]
               (when (and predictive? previous-sample-ms (> sampled-at changed-at) (< stride max-stride) (<= minimum max-stride)
                          (>= (min previous-sample-ms last-sample-ms cost-ms) min-cost-ms))
                 [id (/ cost-ms stride) changed-at])))
       (sort-by (fn [[id saving changed-at]] [(- saving) changed-at (pr-str id)]))
       ffirst))

(defn- faster-stride [stride minimum]
  (let [halved (quot stride 2)]
    (if (< halved minimum) 1 halved)))

(defn- recovery-candidate [entries minimum free-ms]
  (->> entries
       (keep (fn [[id {:keys [cost-ms stride changed-at]}]]
               (when (> stride 1)
                 (let [next-stride (faster-stride stride minimum)
                       cost (* cost-ms (- (/ 1.0 next-stride) (/ 1.0 stride)))]
                   (when (<= cost free-ms) [id changed-at cost])))))
       (sort-by (fn [[id changed-at cost]] [changed-at cost (pr-str id)]))
       ffirst))

(defn advance
  "Fold a completed frame into the release policy. :versions maps active instance
  IDs to their definition identities/versions. Optional :max-strides maps active
  IDs to individual whole-frame limits. Optional :output-slot is the index
  of the physical deadline rendered. Epoch changes start a fresh history.
  :samples comes from observer, :period-ms is the actual output period and
  :elapsed-ms includes complete host work. Only eligible expensive effects slow
  down. Each pressure window can slow one effect. Two real cheap samples
  restore that instance regardless of the scene load. State is disposable."
  [previous {:keys [epoch versions samples period-ms elapsed-ms max-strides output-slot] :as timings} config]
  (when-not (and (time/finite-number? period-ms) (pos? period-ms)
                 (time/finite-number? elapsed-ms) (not (neg? elapsed-ms)))
    (throw (ex-info "Frame timings require a positive period and nonnegative elapsed time" {})))
  (when-not (or (nil? max-strides) (and (map? max-strides) (every? pos-int? (vals max-strides))))
    (throw (ex-info "Per-effect maximum strides must be positive frame counts" {:max-strides max-strides})))
  (when-not (or (nil? output-slot) (nat-int? output-slot))
    (throw (ex-info "Physical output slot must be a nonnegative integer" {:output-slot output-slot})))
  (let [{:keys [smoothing headroom pressure-frames recovery-frames max-stride]} config
        prior (when (= epoch (:epoch previous)) previous)
        ;; A producer which regularly skips physical slots can overshoot its
        ;; forecast. Restarting that window costs both a current and a future
        ;; evaluation. Require room for two actual render opportunities before
        ;; spending those calls, after two consecutive observed gaps.
        gap (when (and output-slot (:output-slot prior) (> output-slot (:output-slot prior)))
              (- output-slot (:output-slot prior)))
        minimum (if (and gap (:slot-gap prior)) (+ gap (:slot-gap prior)) 2)
        frame (inc (:frame prior 0))
        entries (reduce-kv (fn [m id version]
                             (assoc m id (update-entry (get-in prior [:effects id]) version
                                                       (get samples id) config frame
                                                       (min max-stride (get max-strides id max-stride)) minimum))) {} versions)
        measured (smooth (:frame-ms prior) elapsed-ms smoothing)
        budget (* period-ms (- 1.0 headroom))
        missed (smooth (:late-rate prior) (if (> elapsed-ms period-ms) 1.0 0.0) smoothing)
        pressure? (or (> measured budget) (> missed 0.25))
        quiet? (and (< measured (* 0.85 budget)) (< missed 0.1))
        hot (if pressure? (inc (:over-budget-frames prior 0)) 0)
        cool (if quiet? (inc (:under-budget-frames prior 0)) 0)
        slow (when (and (not (:defer-live-slowdown? timings)) (>= hot pressure-frames) (> elapsed-ms budget))
               (slowdown-candidate entries minimum config))
        fast (when (and (>= cool recovery-frames) (< elapsed-ms budget))
               (recovery-candidate entries minimum (- budget measured)))
        changed (or slow fast)
        effects (cond-> entries
                  slow (update-in [slow :stride] #(min (get-in entries [slow :max-stride]) (max minimum (* 2 %))))
                  fast (update-in [fast :stride] faster-stride minimum)
                  changed (assoc-in [changed :changed-at] frame))]
    {:epoch epoch :frame frame :effects effects :frame-ms measured :late-rate missed
     :output-slot output-slot :slot-gap gap :minimum-useful-stride minimum
     :over-budget-frames (if slow 0 hot) :under-budget-frames (if fast 0 cool)
     :keyframe-intervals (into {} (keep (fn [[id {:keys [stride]}]]
                                         (when (> stride 1) [id {:ms (* period-ms stride)}]))) effects)}))


(defn ranked-costs
  "Measured full evaluations, most expensive first. Effects without a completed
  sample have no estimate and are omitted."
  [state]
  (->> (:effects state)
       (keep (fn [[id entry]]
               (when (:cost-ms entry)
                 (assoc (select-keys entry [:cost-ms :predictive? :stride :max-stride :evaluations :sampled-frames]) :instance-id id))))
       (sort-by (juxt (comp - :cost-ms) (comp pr-str :instance-id)))
       vec))

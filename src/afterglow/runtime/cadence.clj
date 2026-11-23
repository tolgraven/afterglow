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

(defn- update-entry [entry version sample {:keys [smoothing max-stride min-cost-ms]} frame]
  (let [prior (if (and entry (= version (:version entry))) entry
                {:version version :stride 1 :changed-at frame})
        {:keys [previous-sample-ms last-sample-ms predictive?] :as updated}
        (cond-> prior sample (record-sample sample smoothing frame))
        cheap? (and previous-sample-ms (< (max previous-sample-ms last-sample-ms) min-cost-ms))]
    (if (and (> (:stride updated) 1) (or cheap? (false? predictive?)))
      (assoc updated :stride 1 :changed-at frame)
      (update updated :stride min max-stride))))

(defn- slowdown-candidate [entries {:keys [max-stride min-cost-ms]}]
  (->> entries
       (keep (fn [[id {:keys [predictive? cost-ms stride changed-at sampled-at previous-sample-ms last-sample-ms]}]]
               (when (and predictive? previous-sample-ms (> sampled-at changed-at) (< stride max-stride)
                          (>= (min previous-sample-ms last-sample-ms cost-ms) min-cost-ms))
                 [id (/ cost-ms stride) changed-at])))
       (sort-by (fn [[id saving changed-at]] [(- saving) changed-at (pr-str id)]))
       ffirst))

(defn- recovery-candidate [entries free-ms]
  (->> entries
       (keep (fn [[id {:keys [cost-ms stride changed-at]}]]
               (when (> stride 1)
                 (let [next-stride (max 1 (quot stride 2))
                       cost (* cost-ms (- (/ 1.0 next-stride) (/ 1.0 stride)))]
                   (when (<= cost free-ms) [id changed-at cost])))))
       (sort-by (fn [[id changed-at cost]] [changed-at cost (pr-str id)]))
       ffirst))

(defn advance
  "Fold a completed frame into the release policy. :versions maps active instance
  IDs to their definition identities/versions. Epoch changes start a fresh history.
  :samples comes from observer, :period-ms is the actual output period and
  :elapsed-ms includes complete host work. Only eligible expensive effects slow
  down. Each pressure window can slow one effect. Two real cheap samples
  restore that instance regardless of the scene load. State is disposable."
  [previous {:keys [epoch versions samples period-ms elapsed-ms]} config]
  (when-not (and (time/finite-number? period-ms) (pos? period-ms)
                 (time/finite-number? elapsed-ms) (not (neg? elapsed-ms)))
    (throw (ex-info "Frame timings require a positive period and nonnegative elapsed time" {})))
  (let [{:keys [smoothing headroom pressure-frames recovery-frames max-stride]} config
        prior (when (= epoch (:epoch previous)) previous)
        frame (inc (:frame prior 0))
        entries (reduce-kv (fn [m id version]
                             (assoc m id (update-entry (get-in prior [:effects id]) version
                                                       (get samples id) config frame))) {} versions)
        measured (smooth (:frame-ms prior) elapsed-ms smoothing)
        budget (* period-ms (- 1.0 headroom))
        missed (smooth (:late-rate prior) (if (> elapsed-ms period-ms) 1.0 0.0) smoothing)
        pressure? (or (> measured budget) (> missed 0.25))
        quiet? (and (< measured (* 0.85 budget)) (< missed 0.1))
        hot (if pressure? (inc (:over-budget-frames prior 0)) 0)
        cool (if quiet? (inc (:under-budget-frames prior 0)) 0)
        slow (when (and (>= hot pressure-frames) (> elapsed-ms budget))
               (slowdown-candidate entries config))
        fast (when (and (>= cool recovery-frames) (< elapsed-ms budget))
               (recovery-candidate entries (- budget measured)))
        changed (or slow fast)
        effects (cond-> entries
                  slow (update-in [slow :stride] #(min max-stride (* 2 %)))
                  fast (update-in [fast :stride] #(max 1 (quot % 2)))
                  changed (assoc-in [changed :changed-at] frame))]
    {:epoch epoch :frame frame :effects effects :frame-ms measured :late-rate missed
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
                 (assoc (select-keys entry [:cost-ms :predictive? :stride :evaluations :sampled-frames]) :instance-id id))))
       (sort-by (juxt (comp - :cost-ms) (comp pr-str :instance-id)))
       vec))

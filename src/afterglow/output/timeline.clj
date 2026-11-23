(ns afterglow.output.timeline
  "Pure planning for a phase-locked physical output clock, in monotonic milliseconds."
  (:require [afterglow.time :as time]))

(defn timeline [origin-ms period-ms]
  (when-not (and (time/finite-number? origin-ms) (not (neg? origin-ms))
                 (time/finite-number? period-ms) (pos? period-ms))
    (throw (ex-info "A physical timeline needs a finite origin and positive period" {})))
  {:origin-ms origin-ms :period-ms period-ms :slot 0 :costs [] :wake-lags []
   :renders 0 :on-time 0 :skipped 0 :missed-wakes 0})

(defn slot-at
  "Most recent nominal deadline at or before now."
  [{:keys [origin-ms period-ms]} now]
  (long (Math/floor (/ (- now origin-ms) period-ms))))

(defn deadline [{:keys [origin-ms period-ms]} slot]
  (+ origin-ms (* slot period-ms)))

(defn- record [history value]
  (conj (if (= 24 (count history)) (into [] (subvec history 1)) history) value))

(defn- recent-upper [history]
  (let [ordered (sort history)
        p90 (nth ordered (dec (long (Math/ceil (* 0.90 (count ordered))))))]
    (max p90 (peek history))))

(defn lead-ms
  "Reserve observed render cost, time to wake the worker and jitter headroom.
  Two successive expensive renders can justify reserving multiple periods."
  [{:keys [costs wake-lags period-ms]}]
  (let [wake (if (seq wake-lags) (min period-ms (recent-upper wake-lags)) 0)]
    (if (seq costs)
      (let [latest (peek costs)
            confirmed (if (> (count costs) 1) (min latest (nth costs (- (count costs) 2))) 0)
            estimate (max confirmed (min period-ms (recent-upper costs)))]
        (+ wake estimate (max 0.4 (* 0.10 estimate))))
      (+ period-ms wake))))

(defn next-render [timeline now]
  (let [{:keys [origin-ms period-ms slot]} timeline
        lead (lead-ms timeline)
        next-slot (max (inc slot) (long (Math/ceil (/ (- (+ now lead) origin-ms) period-ms))))
        due (deadline timeline next-slot)]
    {:slot next-slot :deadline-ms due :start-at-ms (- due lead) :lead-ms lead}))

(defn- wake-lag [ticket started]
  (max 0 (- started (:start-at-ms ticket))))

(defn missed-wake
  "The OS released the worker after its slot. Reserve the observed wake lag
  on the next attempt even when no effect could run in this one."
  [state ticket started]
  (-> state
      (update :wake-lags record (wake-lag ticket started))
      (update :skipped + (- (:slot ticket) (:slot state)))
      (update :missed-wakes inc)
      (assoc :slot (:slot ticket)
             :last-missed-wake (assoc ticket :started-at-ms started))))

(defn observed
  "Record when the rendered output was handed off. Aborted evaluations have no
  ready timestamp. Finish may include later bookkeeping and observers."
  [{:keys [slot] :as state} ticket started ready finished]
  (let [duration (- (or ready finished) started)
        due (:deadline-ms ticket)
        on-time? (and ready (<= ready due))]
    (-> state
        (update :renders inc)
        (update :on-time + (if on-time? 1 0))
        (update :skipped + (- (:slot ticket) slot 1))
        (update :costs record duration)
        (update :wake-lags record (wake-lag ticket started))
        (assoc :slot (:slot ticket)
               :last (assoc ticket :started-at-ms started :ready-at-ms ready :finished-at-ms finished
                            :cost-ms duration :wake-lag-ms (wake-lag ticket started) :slack-ms (when ready (- due ready)))))))

(defn next-output-slot
  "Stay on the common grid. After an overrun or a severely delayed wake, leave
  at least half a period after the previous handoff returned. This upper
  bound on actual sink entry also covers a preemption just before the call."
  [{:keys [origin-ms period-ms] :as timeline} slot handed-off finished]
  (max (inc slot) (inc (slot-at timeline finished))
       (long (Math/ceil (/ (- (+ handed-off (/ period-ms 2)) origin-ms) period-ms)))))

(ns afterglow.output.timeline
  "Pure planning for a phase-locked physical output clock, in monotonic milliseconds."
  (:require [afterglow.time :as time]))

(defn timeline [origin-ms period-ms]
  (when-not (and (time/finite-number? origin-ms) (not (neg? origin-ms))
                 (time/finite-number? period-ms) (pos? period-ms))
    (throw (ex-info "A physical timeline needs a finite origin and positive period" {})))
  {:origin-ms origin-ms :period-ms period-ms :slot 0 :costs [] :renders 0 :on-time 0 :skipped 0})

(defn slot-at
  "Most recent nominal deadline at or before now."
  [{:keys [origin-ms period-ms]} now]
  (long (Math/floor (/ (- now origin-ms) period-ms))))

(defn deadline [{:keys [origin-ms period-ms]} slot]
  (+ origin-ms (* slot period-ms)))

(defn lead-ms
  "Reserve the recent upper render cost plus jitter headroom. A single cold
  spike can use a full period. Repeated expensive renders can request several."
  [{:keys [costs period-ms]}]
  (if (seq costs)
    (let [ordered (sort costs)
          p90 (nth ordered (dec (long (Math/ceil (* 0.90 (count ordered))))))
          last-cost (peek costs)
          confirmed (if (> (count costs) 1) (min last-cost (nth costs (- (count costs) 2))) 0)
          estimate (max confirmed (min period-ms (max p90 last-cost)))]
      (+ estimate (max 0.4 (* 0.10 estimate))))
    period-ms))

(defn next-render [timeline now]
  (let [{:keys [origin-ms period-ms slot]} timeline
        lead (lead-ms timeline)
        next-slot (max (inc slot) (long (Math/ceil (/ (- (+ now lead) origin-ms) period-ms))))
        due (deadline timeline next-slot)]
    {:slot next-slot :deadline-ms due :start-at-ms (- due lead) :lead-ms lead}))

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
        (update :costs #(conj (if (= 24 (count %)) (into [] (subvec % 1)) %) duration))
        (assoc :slot (:slot ticket)
               :last (assoc ticket :started-at-ms started :ready-at-ms ready :finished-at-ms finished
                            :cost-ms duration :slack-ms (when ready (- due ready)))))))

(defn next-output-slot
  "Stay on the common grid. After an overrun or a severely delayed wake, leave
  at least half a period between physical sends instead of producing a burst."
  [{:keys [origin-ms period-ms] :as timeline} slot started finished]
  (max (inc slot) (inc (slot-at timeline finished))
       (long (Math/ceil (/ (- (+ started (/ period-ms 2)) origin-ms) period-ms)))))

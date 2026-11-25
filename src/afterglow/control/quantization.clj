(ns afterglow.control.quantization
  "Pure cue launch scheduling on the show owner's authoritative transport.
  Within one owner boundary, apply each due command using the admission clock
  and settle its receipt before processing another input or invalidation."
  (:require [afterglow.time :as time])
  (:import (java.math BigDecimal RoundingMode)))

(defn new-state
  "Create a queue with bounded pending launches, outstanding decisions, and
  completed retry receipts. :pending-limit bounds pending and dispatched queues
  independently. IDs can be retried while their receipts are retained. The
  owner supplies its current :clock-epoch on every transition and invalidates
  it on seeks, source changes, or other clock discontinuities, even when the
  new source reports the same beat or epoch."
  ([] (new-state {}))
  ([{:keys [pending-limit history-limit clock-epoch]
     :or {pending-limit 128 history-limit 1024 clock-epoch 0}}]
   (when-not (and (integer? pending-limit) (pos? pending-limit)
                  (integer? history-limit) (pos? history-limit)
                  (integer? clock-epoch) (not (neg? clock-epoch)))
     (throw (ex-info "Invalid quantization queue limits or epoch"
                     {:pending-limit pending-limit :history-limit history-limit
                      :clock-epoch clock-epoch})))
   {:clock-epoch clock-epoch :pending-limit pending-limit :history-limit history-limit
    :next-order 0 :pending {} :dispatched {} :history {} :history-order []}))

(defn- find-entry [state command-id]
  (or (get-in state [:pending command-id])
      (get-in state [:dispatched command-id])
      (get-in state [:history command-id])))

(defn receipt
  "Return the current status of an intent within the bounded retry window."
  [state command-id]
  (:receipt (find-entry state command-id)))

(defn- remember [state entry]
  (let [command-id (get-in entry [:receipt :command-id])
        order (conj (:history-order state) command-id)
        history (assoc (:history state) command-id entry)]
    (if (> (count order) (:history-limit state))
      (assoc state :history-order (into [] (rest order)) :history (dissoc history (first order)))
      (assoc state :history-order order :history history))))

(defn- fail! [code message]
  (throw (ex-info message {:quantization/error code})))

(defn- position [{:keys [time-ms beat]}]
  (when-not (and (time/finite-number? time-ms) (not (neg? time-ms))
                 (time/finite-number? beat))
    (fail! :invalid-clock "Clock requires finite beat and nonnegative logical time"))
  {:time-ms time-ms :beat beat})

(defn- playing? [clock]
  (let [playing (:playing? clock)]
    (when-not (boolean? playing)
      (fail! :invalid-clock "Grid scheduling requires a transport playing state"))
    playing))

(defn- exact [value]
  (let [value (rationalize value)]
    (if (integer? value) (bigint value) value)))

(defn- boundary-coordinates [beat]
  (let [decimal (if (ratio? beat)
                  (let [denominator (bigdec (denominator beat))
                        ;; IEEE double midpoints are dyadic with denominators up to
                        ;; 2^1075. This scale preserves ties and cannot cross one.
                        scale (int (max 1075 (+ 324 (.precision denominator))))]
                    (.divide (bigdec (numerator beat)) denominator scale RoundingMode/DOWN))
                  (bigdec beat))]
    {:exact beat :double (.doubleValue ^BigDecimal decimal) :float (.floatValue ^BigDecimal decimal)}))

(defn- compare-beat [beat boundary]
  ;; A transport reported as a float can land exactly on a recurring fraction
  ;; at its own precision. The immediately adjacent floats remain distinct.
  (cond
    (instance? Double beat) (compare beat (:double boundary))
    (instance? Float beat) (compare beat (:float boundary))
    :else (compare (exact beat) (:exact boundary))))

(defn- grid-boundary [grid {:keys [beat meter grid-origin-beat] :or {grid-origin-beat 0}}]
  (when-not (and (empty? (time/validate-duration grid))
                 (not (contains? grid :ms)) (pos? (val (first grid)))
                 (time/finite-number? grid-origin-beat))
    (fail! :invalid-grid "Grid requires one positive beat, bar, or phrase interval and a finite origin"))
  (when-not (or (nil? meter) (map? meter))
    (fail! :invalid-clock "Clock meter must be a map"))
  (let [meter (time/normalize-meter meter)
        [unit amount] (first grid)
        interval (time/duration->beats {unit (exact amount)} (update meter :beats-per-bar exact))
        origin (exact grid-origin-beat)
        offset (- (exact beat) origin)
        quotient (quot offset interval)
        floor (if (< offset (* quotient interval)) (dec quotient) quotient)
        lower (+ origin (* floor interval))
        lower-boundary (boundary-coordinates lower)
        boundary (if (pos? (compare-beat beat lower-boundary))
                   (boundary-coordinates (+ lower interval)) lower-boundary)]
    (when-not (time/finite-number? (:double boundary))
      (fail! :invalid-grid "Grid boundary exceeds finite beat range"))
    {:grid-info {:meter meter :grid-origin-beat grid-origin-beat :interval-beats interval
                 :due-beat (:exact boundary)}
     :boundary boundary}))

(defn- reject [state command-id reason]
  {:state state :due [] :receipt {:command-id command-id :status :rejected :reason reason}})

(defn- dispatch [state {:keys [request receipt] :as entry} at]
  (let [id (:command-id receipt)
        result (assoc receipt :status :due :dispatched-at at)]
    [(-> state (update :pending dissoc id) (assoc-in [:dispatched id] (assoc entry :receipt result)))
     (assoc result :command (:command request))]))

(defn admit
  "Submit an immutable :cue/launch command with a stable :command-id. A missing
  :grid or explicit :off returns an immediate decision. A musical grid waits
  for tick, even at an exact boundary. :raw may supply original :time-ms and/or
  :beat; scheduling uses the flat authoritative clock at submission. Pending
  launches capture its meter and optional :grid-origin-beat (default zero).
  A retry returns the current receipt with :duplicate?. Reusing an ID for a
  changed command, grid, or raw input is a conflict."
  [state {:keys [command grid raw] :or {grid :off}} clock]
  (let [id (:command-id command)
        request {:command command :grid grid :raw raw}
        existing (find-entry state id)]
    (cond
      (not= (:clock-epoch state) (:clock-epoch clock)) (reject state id :stale-clock-epoch)
      (not (and (map? command) (= :cue/launch (:op command))
                (or (keyword? id) (and (string? id) (not (empty? id))))))
      (reject state id :invalid-launch-intent)

      existing (if (= request (:request existing))
                 {:state state :due [] :receipt (:receipt existing) :duplicate? true}
                 (reject state id :command-id-conflict))
      (and (= grid :off) (>= (count (:dispatched state)) (:pending-limit state)))
      (reject state id :dispatch-full)
      (and (not= grid :off) (>= (count (:pending state)) (:pending-limit state)))
      (reject state id :queue-full)

      :else
      (try
        (let [at (position clock)
              raw (if (nil? raw) at
                      (do (when-not (and (map? raw)
                                        (every? time/finite-number? (vals (select-keys raw [:time-ms :beat]))))
                            (fail! :invalid-raw-time "Raw timing must supply finite coordinates"))
                          (merge at (select-keys raw [:time-ms :beat]))))
              {:keys [grid-info boundary]} (when-not (= grid :off) (grid-boundary grid clock))
              result (merge {:command-id id :clock-epoch (:clock-epoch state) :order (:next-order state)
                             :status :pending :mode (get-in command [:launch :mode] :persistent)
                             :grid grid :raw raw :requested-at at} grid-info)
              entry {:request request :receipt result :boundary boundary}
              state (update state :next-order inc')]
          (if (= grid :off)
            (let [[state decision] (dispatch state entry at)]
              {:state state :receipt (receipt state id) :due [decision]})
            {:state (assoc-in state [:pending id] entry) :receipt result :due []}))
        (catch clojure.lang.ExceptionInfo error
          (reject state id (get (ex-data error) :quantization/error :invalid-grid)))))))

(defn tick
  "Return due decisions once, in due beat order and then admission order. A
  paused transport holds queued launches. Ordinary sampled progress may cross
  a due beat and dispatch on the first later tick. The owner must invalidate
  before feeding a seek or source discontinuity. BPM is irrelevant. Re-stamp
  the returned commands with the logical time from the actual admission clock."
  [state clock]
  (cond
    (not= (:clock-epoch state) (:clock-epoch clock)) {:state state :due [] :reason :stale-clock-epoch}
    (not (playing? clock)) {:state state :due []}
    :else
    (let [at (position clock)
          capacity (- (:pending-limit state) (count (:dispatched state)))
          due (->> (vals (:pending state))
                   (filter #(not (neg? (compare-beat (:beat at) (:boundary %)))))
                   (sort-by (juxt #(get-in % [:receipt :due-beat]) #(get-in % [:receipt :order])))
                   (take capacity))]
      (reduce (fn [{:keys [state due]} entry]
                (let [[state decision] (dispatch state entry at)]
                  {:state state :due (conj due decision)}))
              {:state state :due []} due))))

(defn cancel
  "Cancel a pending intent by ID. A :held-release only cancels held launches.
  After dispatch the owner handles held release by actual instance identity."
  [state command-id clock-epoch reason]
  (let [{current :receipt :as entry} (find-entry state command-id)]
    (cond
      (not= (:clock-epoch state) clock-epoch) (reject state command-id :stale-clock-epoch)
      (nil? current) (reject state command-id :unknown-intent)
      (not= :pending (:status current)) {:state state :receipt current :due []}
      (and (= reason :held-release) (not= :held (:mode current))) (reject state command-id :not-held)
      (not (keyword? reason)) (reject state command-id :invalid-reason)
      :else
      (let [result (assoc current :status :cancelled :reason reason)]
        {:state (remember (update state :pending dissoc command-id) (assoc entry :receipt result))
         :receipt result :due []}))))

(defn settle
  "Record the usual cue admission result for a due decision. Supply the actual
  admission clock and whether launch succeeded. A failed admission records the
  attempted time and a distinct :missed receipt. Repeated settlement is inert."
  [state command-id clock launched?]
  (let [{current :receipt :as entry} (find-entry state command-id)]
    (cond
      (not= (:clock-epoch state) (:clock-epoch clock)) (reject state command-id :stale-clock-epoch)
      (nil? current) (reject state command-id :unknown-intent)
      (= :pending (:status current)) (reject state command-id :not-due)
      (not= :due (:status current)) {:state state :receipt current :due []}
      (not (boolean? launched?)) (reject state command-id :invalid-admission)
      :else
      (let [at (position clock)
            result (if launched?
                     (assoc current :status :fired :admitted-at at)
                     (assoc current :status :missed :reason :launch-rejected :attempted-at at))]
        {:state (remember (update state :dispatched dissoc command-id) (assoc entry :receipt result))
         :receipt result :due []}))))

(defn invalidate
  "Advance the clock epoch and mark every outstanding launch missed. Supply
  the previous epoch and a reason such as :seek or :source-changed. The next
  observation must use the returned epoch. Stale invalidations are inert."
  [state clock-epoch reason]
  (cond
    (not= (:clock-epoch state) clock-epoch) {:state state :missed [] :reason :stale-clock-epoch}
    (not (keyword? reason)) {:state state :missed [] :reason :invalid-reason}
    :else
    (let [open (concat (vals (:pending state)) (vals (:dispatched state)))
          missed (mapv #(update % :receipt assoc :status :missed :reason reason)
                       (sort-by #(get-in % [:receipt :order]) open))]
      {:state (reduce remember (-> state (update :clock-epoch inc') (assoc :pending {} :dispatched {})) missed)
       :missed (mapv :receipt missed)})))

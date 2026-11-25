(ns afterglow.output.scheduler
  "Owned physical output clock. Effect evaluation only hands over immutable
  completions; the publisher never takes the show-owner lock or runs effects."
  (:require [afterglow.render.presentation :as policy]
            [afterglow.output.timeline :as timeline])
  (:import [java.util.concurrent ArrayBlockingQueue Executors ScheduledExecutorService TimeUnit]
           [java.util.concurrent.atomic AtomicLong]))

(defn validate-options [options]
  (when-not (map? options) (throw (ex-info "Output presentation must be a map" {})))
  (when (seq (remove #{:mode :period-ms :latency-ms :fade-ms} (keys options)))
    (throw (ex-info "Unknown output presentation setting" {:settings options})))
  (:options (policy/new-state (policy/compile-plan []) options)))

(defn create
  "Inert owner; send! receives newly owned universe arrays and a packet ID.
  Optional prepare-output receives those arrays and the source metadata and
  returns the final universe map before deadline admission. Optional
  prepare-safety-output receives a private copy of the last successfully sent
  arrays, or current idle arrays if the initial send threw. Its metadata includes
  :wire-patch from the last complete send, :stale-source? for an older source
  generation, and :uncertain? for a possible partial send. Return nil or corrected
  buffers using the current gate's patch.

  For time-bounded safety state, optional output-valid-until-ms receives the
  preparation metadata and monotonic time immediately before preparation. It
  returns the earliest boundary strictly after that time, or nil. If packing
  crosses it while the slot is still eligible, prepare again from fresh buffers.
  Both preparation hooks receive the current gate's optional :output-context.
  now-ms supplies the monotonic clock."
  [{:keys [send! prepare-output prepare-safety-output output-valid-until-ms now-ms receipt-capacity]}]
  (let [origin (System/nanoTime)]
    {:send! send! :prepare-output prepare-output :prepare-safety-output prepare-safety-output
     :output-valid-until-ms output-valid-until-ms
     :wire (when (and send! prepare-safety-output) (atom nil))
     :now-ms (or now-ms #(/ (- (System/nanoTime) origin) 1.0e6))
     :gate (atom nil) :counter (atom 0)
     :receipts (when receipt-capacity (ArrayBlockingQueue. (int receipt-capacity)))
     :receipt-drops (AtomicLong. 0)
     :queue (atom []) :lock (Object.) :closed? (atom false)
     :scheduler (atom nil) :timeline (atom nil) :ready (atom nil) :state (atom nil)
     :status (atom {:published 0 :coalesced 0})}))

(defn- gate! [owner epoch patch options dark? {:keys [timeline-id output-context]}]
  (let [key [epoch patch options (boolean dark?) timeline-id]
        current @(:gate owner)]
    (when-not @(:closed? owner)
      (if (= key (:key current))
        current
        (locking (:lock owner)
          (when-not @(:closed? owner)
            (let [latest @(:gate owner)]
              (if (= key (:key latest))
                latest
                (reset! (:gate owner)
                        (cond-> {:key key :generation (inc (:generation latest 0))
                                 :epoch epoch :plan (policy/compile-plan patch)
                                 :options (dissoc (validate-options options) :epoch)
                                 :dark? (boolean dark?)}
                          (some? output-context) (assoc :output-context output-context)))))))))))

(defn begin-frame!
  "Capture a completion identity before evaluation. Epoch/patch/policy/darkness
  changes invalidate all older completions and buffered bright frames. The
  optional ticket's :output-context belongs to the newly opened gate and
  remains stable while that gate is reused."
  ([owner epoch patch options dark?] (begin-frame! owner epoch patch options dark? nil))
  ([owner epoch patch options dark? ticket]
   (when-let [gate (gate! owner epoch patch options dark? ticket)]
     (cond-> {:generation (:generation gate) :epoch epoch :frame-id (swap! (:counter owner) inc)
              :time-ms (if (:slot ticket) (:deadline-ms ticket) ((:now-ms owner)))}
       (:slot ticket) (merge (select-keys ticket [:slot :started-at-ms :inputs-at-ms]))))))

(defn- publication-expiry [grid token period-ms latency-ms]
  ;; A sample ready by its delayed target can first become the lower endpoint
  ;; on the next physical slot, even if the requested latency is fractional.
  (let [period (get grid :period-ms period-ms)
        slots (long (Math/ceil (/ latency-ms period)))]
    (if grid
      (timeline/deadline grid (+ (:slot token) slots))
      (+ (:time-ms token) (* slots period)))))

(defn- enqueue! [owner entry]
  (let [append (fn [pending]
                 (if (and (some? pending) (= (:generation entry) (:generation @(:gate owner))))
                   (if (< (count pending) 3)
                     (conj pending entry)
                     (conj (into [] (next pending)) entry))
                   pending))
        [before after] (swap-vals! (:queue owner) append)]
    (when-not (identical? before after)
      (when (= 3 (count before))
        (swap! (:status owner) update :coalesced inc))
      true)))

(defn complete!
  "Freeze an exclusively owned renderer result and offer without blocking the
  evaluator. An optional immutable :safety-state on rendered follows this
  source through the preparation callbacks. At most three completions wait;
  excess oldest packets coalesce."
  [owner token rendered]
  (when (and token (not @(:closed? owner))
             (= (:generation token) (:generation @(:gate owner))))
    (let [now (:now-ms owner)
          frozen (policy/freeze-frame (assoc token :completed-at-ms (now)) rendered)
          marker (:calibration token)
          verified (cond-> frozen marker
                   (assoc :calibration (dissoc marker :expected-bytes)
                          :calibration-verified?
                          (every? (fn [[[universe index] value]]
                                    (= value (get-in frozen [:universes universe index]))) (:expected-bytes marker))))
          ready (now)
          packet (cond-> (assoc verified :completed-at-ms ready)
                   (:inputs-at-ms token) (assoc :inputs-at-ms (:inputs-at-ms token))
                   (:safety-state rendered) (assoc :safety-state (:safety-state rendered)))
          options (:options @(:gate owner))
          latency (if (= :buffered-interpolation (:mode options)) (:latency-ms options) 0)
          due (when (:slot token) (+ (:time-ms token) latency))
          expiry (when due (publication-expiry @(:timeline owner) token (:period-ms options) latency))
          entry {:generation (:generation token) :packet packet :due-at-ms expiry}]
      (when (:slot token)
        (reset! (:ready owner) (assoc (select-keys token [:slot :time-ms :show-time-ms :beat :inputs-at-ms]) :ready-at-ms ready)))
      (if (and due (> ready due))
        (do (swap! (:status owner) update :missed-render-deadlines (fnil inc 0)) false)
        (enqueue! owner entry)))))

(defn- admit-completion [gate deadline-ms state {:keys [generation due-at-ms packet]}]
  (cond
    (not= (:generation gate) generation) state
    (and due-at-ms deadline-ms (< due-at-ms deadline-ms))
    (update state :expired-at-publication (fnil inc 0))
    :else
    (let [{next-state :state accepted? :accepted?} (policy/complete state packet)]
      (if accepted?
        (update next-state :history
                (fn [history]
                  (update history (dec (count history)) merge
                          (assoc (select-keys packet [:calibration :calibration-verified? :inputs-at-ms :safety-state])
                                 :due-at-ms due-at-ms))))
        next-state))))

(defn- receipt! [owner gate packet published]
  (when-let [^ArrayBlockingQueue mailbox (when (:calibration packet) (:receipts owner))]
    (let [presentation (:presentation packet) ^AtomicLong drops (:receipt-drops owner)
          receipt {:epoch (:epoch packet) :generation (:generation gate)
                   :frame-id (:frame-id packet) :sample-at-ms (:time-ms packet)
                   :published-at-ms published :presentation presentation :calibration (:calibration packet)
                   :eligible? (boolean (and (:calibration-verified? packet)
                                            (= 1.0 (:gain presentation))
                                            (zero? (:weight presentation 0))
                                            (not (:fallback? presentation))
                                            (not (:waiting? presentation))
                                            (not (:blackout? presentation))))
                   :dropped-before (.get drops)}]
      (if (.offer mailbox receipt) (.set drops 0) (.incrementAndGet drops)))))

(defn- copy-buffers [universes]
  (update-vals universes (fn [^bytes buffer] (aclone buffer))))

(defn- wire-snapshot [packet output]
  (assoc (select-keys packet [:frame-id :time-ms :inputs-at-ms :generation :safety-state :wire-patch])
         :universes (copy-buffers output)))

(defn- handoff! [owner packet output snapshot started]
  (try
    ((:send! owner) output (:frame-id packet))
    (catch Exception error
      (when snapshot (swap! (:wire owner) assoc :uncertain? true))
      (throw error)))
  (let [finished ((:now-ms owner))]
    (when snapshot (reset! (:wire owner) {:last-sent snapshot}))
    (assoc packet :sent-at-ms started :sent-by-ms finished)))

(defn- preparation-context [gate source]
  (cond-> source
    (contains? gate :output-context) (assoc :output-context (:output-context gate))))

(defn- prepare-and-handoff! [owner packet source context prepare! expires-at]
  (let [now (:now-ms owner)
        boundary (when (:safety-state context) (:output-valid-until-ms owner))]
    (loop [checked-at (when boundary (now))]
      (let [valid-until (when boundary (boundary context checked-at))
            _ (when (and (some? valid-until)
                         (not (and (number? valid-until) (Double/isFinite (double valid-until))
                                   (< checked-at valid-until))))
                (throw (ex-info "Output safety boundary must be finite and strictly future" {})))
            output (prepare!)
            snapshot (when (and output (:wire owner)) (wire-snapshot source output))
            started (now)]
        (cond
          (and expires-at (>= started expires-at)) {:expired-before-send? true}
          (and valid-until (>= started valid-until)) (recur started)
          output (handoff! owner packet output snapshot started))))))

(defn- send-safety-output! [owner gate]
  (let [{:keys [last-sent uncertain?]} (some-> (:wire owner) deref)]
    (when (or last-sent uncertain?)
      (let [source (if last-sent (dissoc last-sent :universes :wire-patch)
                       {:frame-id 0 :generation (:generation gate)})
            context (preparation-context gate (assoc source :wire-patch (:wire-patch last-sent)
                                                           :uncertain? (boolean uncertain?)
                                                           :stale-source? (not= (:generation gate) (:generation source))))
            output-source (assoc source :wire-patch (get-in gate [:key 1]))
            prepare! (fn []
                       (let [buffers (if last-sent (copy-buffers (:universes last-sent))
                                         (:universes (policy/materialize {:universes (get-in gate [:plan :idle-universes])})))]
                         ((:prepare-safety-output owner) buffers context)))]
        (when-let [sent (prepare-and-handoff! owner source output-source context prepare! nil)]
          (assoc sent :safety-output? true))))))

(defn- send-packet! [owner gate packet expires-at]
  (if (:send! owner)
    (let [source (assoc packet :generation (:generation gate) :wire-patch (get-in gate [:key 1]))
          context (preparation-context gate (select-keys packet [:frame-id :safety-state]))
          prepare! (fn []
                     (let [{:keys [universes]} (policy/materialize packet)]
                       (if-let [prepare (:prepare-output owner)] (prepare universes context) universes)))
          sent (prepare-and-handoff! owner packet source context prepare! (when-not (:dark? gate) expires-at))]
      (if (:expired-before-send? sent)
        (assoc (send-safety-output! owner gate) :expired-before-send? true)
        (when sent
          (receipt! owner gate packet (:sent-by-ms sent))
          sent)))
    packet))

(defn- current-policy [gate previous deadline-ms]
  (if (= (:generation previous) (:generation gate))
    (let [state (:policy previous)
          history (:history state)
          expired? (fn [{:keys [due-at-ms frame-id]}]
                     (and due-at-ms deadline-ms (< due-at-ms deadline-ms)
                          (not= frame-id (:last-source previous))))
          expired (count (filter expired? history))]
      (if (zero? expired) state
          (-> state (assoc :history (filterv (complement expired?) history))
              (update :expired-at-publication (fnil + 0) expired))))
    (policy/new-state (:plan gate) (assoc (:options gate) :epoch (:epoch gate)))))

(defn- keep-presented-source [state previous gate]
  ;; Three accepted future endpoints can occupy the entire policy history.
  ;; Keep the actual lower source as well, with its original bytes and time,
  ;; so direct hold, a fresh fade, or a buffered interpolation can use it.
  (if (and (= (:generation gate) (:generation previous))
           (:last-source previous)
           (or (empty? (:history state))
               (> (:frame-id (first (:history state))) (:last-source previous))))
    (if-let [held (some #(when (= (:last-source previous) (:frame-id %)) %)
                        (get-in previous [:policy :history]))]
      (update state :history #(into [held] %))
      state)
    state))

(defn- dark-packet [gate packet now]
  {:frame-id (:frame-id packet 0) :epoch (:epoch gate)
   :calibration (:calibration packet) :calibration-verified? false
   :universes (get-in gate [:plan :idle-universes])
   :presentation {:mode (get-in gate [:options :mode]) :presented-at-ms now
                  :blackout? (:dark? gate) :waiting? (nil? packet)}})

(defn- commit-publication! [owner gate state entries packet]
  ;; The producer may have coalesced an entry while the sink was packing.
  ;; Remove only the entries used here, leaving newer arrivals untouched.
  (swap! (:queue owner)
         (fn [pending]
           (cond
             (nil? pending) nil
             (identical? pending entries) []
             :else (let [acknowledged? (fn [entry] (some #(identical? entry %) entries))]
                     (into [] (remove acknowledged?) pending)))))
  (reset! (:state owner) {:generation (:generation gate) :policy state :last-source (:frame-id packet)})
  (swap! (:status owner) #(-> % (update :published inc)
                              (assoc :last (:presentation packet)
                                     :accepted (:accepted state) :dropped (:dropped state)
                                     :expired-at-publication (:expired-at-publication state 0)))))

(defn publish!
  "Present one physical deadline. Safe to call manually with an injected clock.
  Transport work is serialized here, independently from the show/effect owner."
  ([owner] (publish! owner nil))
  ([owner deadline-ms]
   (locking (:lock owner)
     (when-not @(:closed? owner)
       (when-let [gate @(:gate owner)]
         (let [now ((:now-ms owner))
               previous @(:state owner)
               state (current-policy gate previous deadline-ms)
               entries @(:queue owner)
               state (reduce #(admit-completion gate deadline-ms %1 %2) state entries)
               {next-state :state packet :packet} (policy/present (keep-presented-source state previous gate) now)
               packet (if (or (:dark? gate) (nil? packet)) (dark-packet gate packet now) packet)
               period (or (:period-ms @(:timeline owner)) (get-in gate [:options :period-ms]))
               expires-at (when deadline-ms (+ deadline-ms period))
               sent (send-packet! owner gate packet expires-at)]
           (if (:expired-before-send? sent)
             (swap! (:status owner) #(cond-> (update % :expired-before-send (fnil inc 0))
                                      (:safety-output? sent) (update :safety-publications (fnil inc 0))))
             (when (and (not @(:closed? owner)) (= (:generation gate) (:generation @(:gate owner))))
               (commit-publication! owner gate next-state entries packet)))
           sent))))))

(defn drain-receipts!
  "Drain the optional bounded physical-output mailbox off the publisher thread."
  [owner]
  (if-let [^ArrayBlockingQueue mailbox (:receipts owner)]
    (let [result (java.util.ArrayList.)] (.drainTo mailbox result) (vec result)) []))

(defn status [owner]
  (merge @(:status owner) {:scheduled? (some? @(:scheduler owner)) :closed? @(:closed? owner)
                          :pending (count @(:queue owner))
                          :options (:options @(:gate owner))
                          :render-timing (dissoc @(:timeline owner) :costs :wake-lags)}))

(defn- at! [owner ^ScheduledExecutorService executor at-ms f]
  (when-not @(:closed? owner)
    (let [delay (max 0.0 (- at-ms ((:now-ms owner))))]
      (try (.schedule executor ^Runnable f (long (Math/ceil (* delay 1e6))) TimeUnit/NANOSECONDS)
           (catch java.util.concurrent.RejectedExecutionException e
             (when-not @(:closed? owner) (throw e)))))))

(defn- send-slot! [owner grid slot previous started]
  (let [due (timeline/deadline grid slot)
        {:keys [packet error]} (try {:packet (publish! owner due)}
                                    (catch Exception error {:error error}))
        timing (cond-> {:slot slot :deadline-ms due :started-at-ms started :finished-at-ms ((:now-ms owner))
                        :source-time-ms (:time-ms packet) :frame-id (:frame-id packet)
                        :sent-at-ms (:sent-at-ms packet) :sent-by-ms (:sent-by-ms packet)
                        :expired-before-send? (boolean (:expired-before-send? packet))
                        :source-input-age-ms (when (and (:sent-at-ms packet) (:inputs-at-ms packet))
                                               (- (:sent-at-ms packet) (:inputs-at-ms packet)))}
                 (:safety-output? packet) (assoc :safety-output? true)
                 error (assoc :failed? true))]
    (swap! (:status owner) #(cond-> (-> % (assoc :output-timing timing)
                                        (update :skipped-output-slots (fnil + 0) (- slot previous 1)))
                             error (-> (assoc :error (.getMessage ^Exception error))
                                       (update :failed-publications (fnil inc 0)))))
    timing))

(defn- start-publications! [owner executor grid]
  (let [now (:now-ms owner)
        half-period (/ (:period-ms grid) 2.0)]
    (letfn [(queue-slot [wanted previous earliest]
              (at! owner executor (max (timeline/deadline grid wanted) earliest)
                   #(wake wanted previous earliest)))
            (wake [wanted previous earliest]
              ;; Repatch and blackout share this gate. Select the eligible slot
              ;; after any wait for them, so a stalled wake cannot send old work.
              (locking (:lock owner)
                (let [started (now) slot (timeline/slot-at grid started)]
                  (if (or (< slot wanted) (< started earliest))
                    (queue-slot wanted previous earliest)
                    (let [timing (send-slot! owner grid slot previous started)
                          handed-off (or (:sent-by-ms timing)
                                         (when (:failed? timing) (:finished-at-ms timing))
                                         started)
                          finished (now)
                          complete? (and (:sent-by-ms timing) (not (:expired-before-send? timing)))
                          ;; A completed handoff may recover the next nominal
                          ;; slot after the spacing guard opens. Retain the
                          ;; conservative grid wake for failed or expired sends.
                          next-slot (if complete?
                                      (max (inc slot) (inc (timeline/slot-at grid finished)))
                                      (timeline/next-output-slot grid slot handed-off finished))]
                      (queue-slot next-slot slot (+ handed-off half-period)))))))]
      (queue-slot 1 0 (timeline/deadline grid 1)))))

(defn- render-slot! [owner render! ticket started]
  (try (render! (assoc ticket :started-at-ms started))
       (catch Exception error (swap! (:status owner) assoc :render-error (.getMessage error))))
  (let [sample @(:ready owner)
        sample (when (= (:slot ticket) (:slot sample)) sample)
        ticket (merge ticket (select-keys sample [:show-time-ms :beat :inputs-at-ms]))]
    (swap! (:timeline owner) timeline/observed ticket started (:ready-at-ms sample) ((:now-ms owner)))))

(defn- start-renders! [owner executor render! grid]
  (let [now (:now-ms owner) state (:timeline owner)]
    (letfn [(queue-ticket [ticket]
              (at! owner executor (:start-at-ms ticket) #(wake ticket)))
            (wake [ticket]
              (let [start (now)]
                (cond
                  (< start (:start-at-ms ticket)) (queue-ticket ticket)
                  (>= start (:deadline-ms ticket))
                  (queue-ticket (timeline/next-render (swap! state timeline/missed-wake ticket start) start))
                  :else (let [observed (render-slot! owner render! ticket start)]
                          (queue-ticket (timeline/next-render observed (get-in observed [:last :finished-at-ms])))))))]
      (queue-ticket (timeline/next-render grid (:origin-ms grid))))))

(defn start!
  "Own the physical publisher and optional render producer on separate workers.
  The producer receives the next physical deadline and its actual start time."
  ([owner period-ms] (start! owner period-ms nil))
  ([owner period-ms render!]
   (locking (:lock owner)
     (when (or @(:closed? owner) @(:scheduler owner))
       (throw (ex-info "Output publisher is closed or already scheduled" {})))
     (let [grid (timeline/timeline ((:now-ms owner)) period-ms)
           executor (Executors/newScheduledThreadPool (if render! 2 1))]
       (reset! (:scheduler owner) executor)
       (reset! (:timeline owner) grid)
       (start-publications! owner executor grid)
       (when render! (start-renders! owner executor render! grid))))
   owner))

(defn close!
  "Fence late completions and wait only for an already sending transport, never
  an effect worker. The host sends its final physical idle frame after this returns."
  [owner]
  (locking (:lock owner)
    (reset! (:closed? owner) true)
    (when-let [^ScheduledExecutorService scheduler @(:scheduler owner)] (.shutdownNow scheduler))
    (reset! (:queue owner) nil)
    (when-let [^ArrayBlockingQueue mailbox (:receipts owner)] (.clear mailbox))
    (when-let [wire (:wire owner)] (reset! wire nil))
    (reset! (:state owner) nil))
  nil)

(ns afterglow.output.scheduler
  "Owned physical output clock. Effect evaluation only hands over immutable
  completions; the publisher never takes the show-owner lock or runs effects."
  (:require [afterglow.render.presentation :as policy]
            [afterglow.output.timeline :as timeline])
  (:import [java.util.concurrent LinkedBlockingDeque ArrayBlockingQueue Executors ScheduledExecutorService TimeUnit]
           [java.util.concurrent.atomic AtomicLong]))

(defn validate-options [options]
  (when-not (map? options) (throw (ex-info "Output presentation must be a map" {})))
  (when (seq (remove #{:mode :period-ms :latency-ms :fade-ms} (keys options)))
    (throw (ex-info "Unknown output presentation setting" {:settings options})))
  (:options (policy/new-state (policy/compile-plan []) options)))

(defn create
  "Inert owner; send! receives newly owned universe arrays and a packet ID.
  now-ms is a physical monotonic clock, never the musical/show clock."
  [{:keys [send! now-ms receipt-capacity]}]
  (let [origin (System/nanoTime)]
    {:send! send! :now-ms (or now-ms #(/ (- (System/nanoTime) origin) 1.0e6))
     :gate (atom nil) :counter (atom 0)
     :receipts (when receipt-capacity (ArrayBlockingQueue. (int receipt-capacity)))
     :receipt-drops (AtomicLong. 0)
     :queue (LinkedBlockingDeque. 3) :lock (Object.) :closed? (atom false)
     :scheduler (atom nil) :timeline (atom nil) :ready (atom nil) :state (atom nil)
     :status (atom {:published 0 :coalesced 0})}))

(defn- gate! [owner epoch patch options dark?]
  (let [key [epoch patch options (boolean dark?)]
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
                        {:key key :generation (inc (:generation latest 0))
                         :epoch epoch :plan (policy/compile-plan patch)
                         :options (dissoc (validate-options options) :epoch)
                         :dark? (boolean dark?)})))))))))

(defn begin-frame!
  "Capture a completion identity before evaluation. Epoch/patch/policy/darkness
  changes invalidate all older completions and buffered bright frames."
  ([owner epoch patch options dark?] (begin-frame! owner epoch patch options dark? nil))
  ([owner epoch patch options dark? ticket]
   (when-let [gate (gate! owner epoch patch options dark?)]
     (cond-> {:generation (:generation gate) :epoch epoch :frame-id (swap! (:counter owner) inc)
              :time-ms (if ticket (:deadline-ms ticket) ((:now-ms owner)))}
       ticket (merge (select-keys ticket [:slot :started-at-ms :inputs-at-ms]))))))

(defn complete!
  "Freeze an exclusively owned renderer result and offer without blocking the
  evaluator. At most three completions wait; excess oldest packets coalesce."
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
          packet (assoc verified :completed-at-ms ready)
          options (:options @(:gate owner))
          due (when (:slot token)
                (+ (:time-ms token) (if (= :buffered-interpolation (:mode options)) (:latency-ms options) 0)))
          entry {:generation (:generation token) :packet packet :due-at-ms due}
          ^LinkedBlockingDeque queue (:queue owner)]
      (when (:slot token)
        (reset! (:ready owner) (assoc (select-keys token [:slot :time-ms :show-time-ms :beat :inputs-at-ms]) :ready-at-ms ready)))
      (if (and due (> ready due))
        (do (swap! (:status owner) update :missed-render-deadlines (fnil inc 0)) false)
        (do
          (when-not (.offerLast queue entry)
            (.pollFirst queue)
            (swap! (:status owner) update :coalesced inc)
            (.offerLast queue entry))
          true)))))

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
                          (select-keys packet [:calibration :calibration-verified?]))))
        next-state))))

(defn publish!
  "Present one physical deadline. Safe to call manually with an injected clock.
  Transport work is serialized here, independently from the show/effect owner."
  ([owner] (publish! owner nil))
  ([owner deadline-ms]
  (locking (:lock owner)
    (when-not @(:closed? owner)
      (when-let [gate @(:gate owner)]
        (let [now ((:now-ms owner))
              old @(:state owner)
              state (if (= (:generation old) (:generation gate)) (:policy old)
                        (policy/new-state (:plan gate) (assoc (:options gate) :epoch (:epoch gate))))
              completions (java.util.ArrayList. 3)
              _ (.drainTo ^LinkedBlockingDeque (:queue owner) completions 3)
              state (reduce #(admit-completion gate deadline-ms %1 %2) state completions)
              {next-state :state packet :packet} (policy/present state now)
              packet (if (or (:dark? gate) (nil? packet))
                       {:frame-id (:frame-id packet 0) :epoch (:epoch gate)
                        :calibration (:calibration packet) :calibration-verified? false
                        :universes (get-in gate [:plan :idle-universes])
                        :presentation {:mode (get-in gate [:options :mode]) :presented-at-ms now
                                       :blackout? (:dark? gate) :waiting? (nil? packet)}}
                       packet)]
          (reset! (:state owner) {:generation (:generation gate) :policy next-state})
          ;; A changed gate must not allow a previously bright sample to escape.
          ;; No host code takes this lock while owning a renderer buffer.
          (when (and packet (= (:generation gate) (:generation @(:gate owner))))
            (let [transport (policy/materialize packet)]
              (when-let [send! (:send! owner)]
                (send! (:universes transport) (:frame-id transport))
                ;; No callback or universe copy here. Queue processing is owned
                ;; by the show coordinator, away from the physical deadline.
                (when-let [^ArrayBlockingQueue mailbox (when (:calibration packet) (:receipts owner))]
                  (let [presentation (:presentation packet)
                        ^AtomicLong drops (:receipt-drops owner)
                        receipt {:epoch (:epoch packet) :generation (:generation gate)
                                 :frame-id (:frame-id packet) :sample-at-ms (:time-ms packet)
                                 :published-at-ms ((:now-ms owner)) :presentation presentation
                                 :calibration (:calibration packet)
                                 :eligible? (boolean (and (:calibration-verified? packet)
                                                         (= 1.0 (:gain presentation))
                                                         (zero? (:weight presentation 0))
                                                         (not (:fallback? presentation))
                                                         (not (:waiting? presentation))
                                                         (not (:blackout? presentation))))
                                 :dropped-before (.get drops)}]
                    (if (.offer mailbox receipt) (.set drops 0) (.incrementAndGet drops)))))
              (swap! (:status owner) #(-> % (update :published inc)
                                           (assoc :last (:presentation packet)
                                                  :accepted (:accepted next-state) :dropped (:dropped next-state)
                                                  :expired-at-publication (:expired-at-publication next-state 0))))))
          packet))))))


(defn drain-receipts!
  "Drain the optional bounded physical-output mailbox off the publisher thread."
  [owner]
  (if-let [^ArrayBlockingQueue mailbox (:receipts owner)]
    (let [result (java.util.ArrayList.)] (.drainTo mailbox result) (vec result)) []))

(defn status [owner]
  (merge @(:status owner) {:scheduled? (some? @(:scheduler owner)) :closed? @(:closed? owner)
                          :pending (.size ^LinkedBlockingDeque (:queue owner))
                          :options (:options @(:gate owner))
                          :render-timing (dissoc @(:timeline owner) :costs)}))

(defn- at! [owner ^ScheduledExecutorService executor at-ms f]
  (when-not @(:closed? owner)
    (let [delay (max 0.0 (- at-ms ((:now-ms owner))))]
      (try (.schedule executor ^Runnable f (long (Math/ceil (* delay 1e6))) TimeUnit/NANOSECONDS)
           (catch java.util.concurrent.RejectedExecutionException e
             (when-not @(:closed? owner) (throw e)))))))

(defn- send-slot! [owner grid slot previous started]
  (try
    (let [due (timeline/deadline grid slot)
          packet (publish! owner due)
          timing {:slot slot :deadline-ms due :started-at-ms started :finished-at-ms ((:now-ms owner))
                  :source-time-ms (:time-ms packet) :frame-id (:frame-id packet)}]
      (swap! (:status owner) #(-> % (assoc :output-timing timing)
                                  (update :skipped-output-slots (fnil + 0) (- slot previous 1)))))
    (catch Exception error (swap! (:status owner) assoc :error (.getMessage error)))))

(defn- start-publications! [owner executor grid]
  (let [now (:now-ms owner)]
    (letfn [(queue-slot [wanted previous]
              (at! owner executor (timeline/deadline grid wanted) #(wake wanted previous)))
            (wake [wanted previous]
              ;; Repatch and blackout share this gate. Select the eligible slot
              ;; after any wait for them, so a stalled wake cannot send old work.
              (locking (:lock owner)
                (let [started (now) slot (timeline/slot-at grid started)]
                  (if (< slot wanted)
                    (queue-slot wanted previous)
                    (do (send-slot! owner grid slot previous started)
                        (queue-slot (timeline/next-output-slot grid slot started (now)) slot))))))]
      (queue-slot 1 0))))

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
                  (>= start (:deadline-ms ticket)) (queue-ticket (timeline/next-render @state start))
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
    (.clear ^LinkedBlockingDeque (:queue owner))
    (when-let [^ArrayBlockingQueue mailbox (:receipts owner)] (.clear mailbox))
    (reset! (:state owner) nil))
  nil)

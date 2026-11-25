(ns afterglow.control.clock-test
  (:require [clojure.test :refer :all]
            [afterglow.control.clock :as clock]))

(defn event [state type at & fields]
  (:state (clock/apply-event state (merge {:source-id :midi :type type :time-ms at} (apply hash-map fields)))))

(defn close? [a b] (< (Math/abs (double (- a b))) 1.0e-8))

(deftest midi-system-message-decoding-is-explicit
  (is (= {:type :midi/clock} (clock/decode-midi [248])))
  (is (= {:type :midi/start} (clock/decode-midi [250])))
  (is (= {:type :midi/continue} (clock/decode-midi [251])))
  (is (= {:type :midi/stop} (clock/decode-midi [252])))
  (is (= {:type :midi/song-position :sixteenths 257} (clock/decode-midi [242 1 2])))
  (is (nil? (clock/decode-midi [144 60 127])))
  (doseq [bytes [[] [248 0] [242 128 0] [242 0] [-8]]]
    (is (thrown? clojure.lang.ExceptionInfo (clock/decode-midi bytes)))))

(deftest midi-start-and-ticks-establish-quarter-note-phase-and-tempo
  (let [initial (clock/new-state {:selected-source :midi}) started (event initial :midi/start 0)
        synced (reduce #(event %1 :midi/clock (* %2 (/ 500.0 24))) started (range 49))
        result (clock/snapshot synced 1000.0)]
    (is (= :waiting (:status (clock/snapshot initial 0))))
    (is (false? (get-in (clock/snapshot started 0) [:clock :playing?])))
    (is (= :locked (:status result)))
    (is (close? 120.0 (get-in result [:clock :bpm])))
    (is (close? 2.0 (get-in result [:clock :beat])))
    (is (> (get-in result [:clock :confidence]) 0.99))
    (is (close? 2.5 (get-in (clock/snapshot synced 1250) [:clock :beat])))
    (is (nil? (get-in initial [:sources :midi])))))

(deftest pause-continue-and-song-position-have-distinct-semantics
  (let [started (event (clock/new-state {:selected-source :midi}) :midi/start 0)
        synced (reduce #(event %1 :midi/clock (* %2 (/ 500.0 24))) started (range 25))
        stopped (event synced :midi/stop 510)
        while-stopped (reduce #(event %1 :midi/clock %2) stopped [600 620 640])
        continued (event while-stopped :midi/continue 700)
        resumed (event continued :midi/clock 720)
        sought (event resumed :midi/song-position 730 :sixteenths 32)
        at-position (event sought :midi/clock 750)
        restarted (event at-position :midi/start 760)]
    (is (= 1.0 (get-in (clock/snapshot stopped 1000) [:clock :beat])))
    (is (= 1.0 (get-in (clock/snapshot while-stopped 640) [:clock :beat])))
    (is (= 1.0 (get-in (clock/snapshot resumed 720) [:clock :beat])))
    (is (= 8.0 (get-in (clock/snapshot at-position 750) [:clock :beat])))
    (is (= 0.0 (get-in (clock/snapshot restarted 760) [:clock :beat])))
    (is (> (get-in restarted [:sources :midi :source-epoch]) (get-in resumed [:sources :midi :source-epoch])))))

(deftest selected-source-never-silently-falls-back-and-stale-policy-is-explicit
  (let [event {:type :clock :source-id :live :kind :ableton-live :time-ms 0 :beat 10 :bpm 120 :playing? true :confidence 1}
        held (:state (clock/apply-event (clock/new-state {:selected-source :live :timeout-ms 1000}) event))
        free (:state (clock/apply-event (clock/new-state {:selected-source :live :timeout-ms 1000 :on-stale :freewheel}) event))
        stale (clock/snapshot held 2000)]
    (is (= :stale (:status stale)))
    (is (= 12.0 (get-in stale [:clock :beat])))
    (is (false? (get-in stale [:clock :playing?])))
    (is (zero? (get-in stale [:clock :confidence])))
    (is (= 14.0 (get-in (clock/snapshot free 2000) [:clock :beat])))
    (is (true? (get-in (clock/snapshot free 2000) [:clock :playing?])))
    (is (= :waiting (:status (clock/snapshot (clock/select-source held :missing) 2000))))
    (is (= :manual (:status (clock/snapshot (clock/select-source held :manual) 2000))))))

(deftest duplicate-and-out-of-order-source-events-preserve-state
  (let [state (-> (clock/new-state {:selected-source :midi}) (event :midi/start 0) (event :midi/clock 10))]
    (doseq [[at reason] [[10 :duplicate-tick] [9 :out-of-order]]]
      (let [result (clock/apply-event state {:source-id :midi :type :midi/clock :time-ms at})]
        (is (false? (:accepted? result)))
        (is (= reason (:reason result)))
        (is (= state (:state result)))))))

(deftest beat-link-phase-is-derived-from-beats-not-integer-status-playheads
  (let [base (clock/new-state {:selected-source :deck})
        beat (fn [state at n] (:state (clock/apply-event state {:source-id :deck :type :beat-link/beat :time-ms at
                                                              :bpm 120 :beat-within-bar n :bar-meaningful? true :align-bars? true})))
        first-beat (beat base 1000 3)
        status (:state (clock/apply-event first-beat {:source-id :deck :type :beat-link/status :time-ms 1100
                                                     :bpm 120 :playing? true :reported-beat-number 500}))
        next-beat (beat status 1500 4)
        bar (beat next-beat 2000 1)
        stopped (:state (clock/apply-event bar {:source-id :deck :type :beat-link/status :time-ms 2100
                                                :bpm 120 :playing? false}))]
    (is (= 2.0 (get-in (clock/snapshot first-beat 1000) [:clock :beat])))
    (is (close? 2.2 (get-in (clock/snapshot status 1100) [:clock :beat])))
    (is (= 3.0 (get-in (clock/snapshot next-beat 1500) [:clock :beat])))
    (is (= 4.0 (get-in (clock/snapshot bar 2000) [:clock :beat])))
    (is (= :duplicate-beat (:reason (clock/apply-event bar {:source-id :deck :type :beat-link/beat
                                                           :time-ms 2010 :bpm 120 :beat-within-bar 1}))))
    (is (close? 4.2 (get-in (clock/snapshot stopped 2300) [:clock :beat])))
    (is (= :paused (:status (clock/snapshot stopped 2300))))))

(deftest source-count-and-invalid-values-are-bounded
  (let [state (clock/new-state {:source-limit 1})]
    (is (= :source-limit (:reason (clock/apply-event state {:source-id :other :type :midi/start :time-ms 0})))))
  (doseq [event [{:type :clock :source-id :bad :time-ms 0 :beat Double/NaN :bpm 120 :playing? true :confidence 1}
                {:type :beat-link/beat :source-id :bad :time-ms 0 :bpm 0}
                {:type :midi/song-position :source-id :bad :time-ms 0 :sixteenths -1}]]
    (is (thrown? clojure.lang.ExceptionInfo (clock/apply-event (clock/new-state) event)))))

(deftest marked-forward-seek-advances-source-epoch-but-tempo-change-does-not
  (let [initial (clock/new-state {:selected-source :midi})
        live-event (fn [state at beat bpm & options]
                     (apply event state :clock at :beat beat :bpm bpm :playing? true :confidence 1 options))
        start (live-event initial 0 0.25 120)
        steady (live-event start 250 0.75 60)
        seek (live-event steady 275 32 60 :discontinuity? true)
        next (live-event seek 775 32.5 120)
        observe (fn [state at] (get-in (clock/snapshot state at) [:clock :source-epoch]))]
    (is (= [0 0 1 1] (mapv observe [start steady seek next] [0 250 275 775])))
    (is (== 32 (get-in (clock/snapshot seek 275) [:clock :beat])))))

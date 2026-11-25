(ns afterglow.control.quantization-test
  (:require [afterglow.control.model :as model]
            [afterglow.control.quantization :as quantization]
            [clojure.test :refer [deftest is testing]]))

(defn- clock [beat time-ms]
  {:beat beat :time-ms time-ms :playing? true :clock-epoch 0 :bpm 120})

(defn- launch [id grid]
  {:command {:command-id id :op :cue/launch :cue-id :wash :source :test :show-id :main :epoch 0}
   :grid grid})

(deftest exact-and-neighboring-grid-boundaries
  (doseq [[interval boundary boundary-sample next-boundary]
          [[1/4 5/4 1.25 3/2] [1/3 2/3 (/ 2.0 3.0) 1] [1/3 5/3 (/ 5.0 3.0) 2]
           [0.1M 17/10 1.7 9/5] [1/3 -1/3 (/ -1.0 3.0) 0]]]
    (testing (str "grid " interval ", boundary " boundary)
      (let [state (quantization/new-state)
            request (launch :cue {:beats interval})
            earlier-clock (clock (Math/nextDown boundary-sample) 9)
            boundary-clock (clock boundary-sample 10)
            later-clock (clock (Math/nextUp boundary-sample) 11)
            scheduled (quantization/admit state request earlier-clock)]
        (is (= boundary (get-in scheduled [:receipt :due-beat])))
        (is (= boundary (get-in (quantization/admit state request boundary-clock) [:receipt :due-beat])))
        (is (= boundary (get-in (quantization/admit state request (clock boundary 10)) [:receipt :due-beat])))
        (is (= next-boundary (get-in (quantization/admit state request later-clock) [:receipt :due-beat])))
        (is (empty? (:due (quantization/tick (:state scheduled) earlier-clock))))
        (is (= [:cue] (mapv :command-id (:due (quantization/tick (:state scheduled) boundary-clock)))))))))

(deftest bounded-dispatch-drains-in-order-after-settlement
  (let [initial (quantization/new-state {:pending-limit 1})
        immediate (quantization/admit initial (launch :immediate :off) (clock 3.5 0))
        gridded (quantization/admit (:state immediate) (launch :gridded {:beats 1}) (clock 3.6 50))
        boundary (clock 4 250)
        blocked (quantization/tick (:state gridded) boundary)
        settled (quantization/settle (:state blocked) :immediate (clock 3.6 50) true)
        drained (quantization/tick (:state settled) boundary)]
    (is (empty? (:due blocked)))
    (is (= :pending (:status (quantization/receipt (:state blocked) :gridded))))
    (is (= :dispatch-full
           (get-in (quantization/admit (:state blocked) (launch :other :off) boundary) [:receipt :reason])))
    (is (= [:gridded] (mapv :command-id (:due drained))))
    (is (empty? (:due (quantization/tick (:state drained) boundary))))))

(deftest meter-and-origin-are-captured
  (let [meter {:beats-per-bar 7/2 :bars-per-phrase 3}
        original (assoc (clock 4 100) :meter meter :grid-origin-beat 1/2)
        initial (quantization/new-state)
        bars (quantization/admit initial (launch :bar {:bars 1}) original)
        phrases (quantization/admit (:state bars) (launch :phrase {:phrases 1}) original)
        changed (assoc original :bpm 86 :meter {:beats-per-bar 5} :grid-origin-beat 0)
        {:keys [due state]} (quantization/tick (:state phrases) changed)]
    (is (= {:due-beat 4 :meter meter :grid-origin-beat 1/2 :interval-beats 7/2}
           (select-keys (:receipt bars) [:due-beat :meter :grid-origin-beat :interval-beats])))
    (is (= 11 (get-in phrases [:receipt :due-beat])))
    (is (= [:bar] (mapv :command-id due)))
    (is (empty? (:due (quantization/tick state (assoc changed :beat 10.99 :time-ms 1000)))))
    (is (= [:phrase] (mapv :command-id (:due (quantization/tick state (assoc changed :beat 11 :time-ms 1100))))))))

(deftest captures-actual-cue-admission-in-stable-boundary-order
  (let [show (model/new-show {:registry {:effects {:effect {:id :effect :version 1}}
                                        :cues {:wash {:id :wash :effect-id :effect}}}})
        first-request (assoc (launch :first {:beats 1/4}) :raw {:beat 8.04 :time-ms 89})
        second-request (launch :second {:beats 1/4})
        early (quantization/admit (quantization/new-state) first-request (clock 8.08 100))
        late (quantization/admit (:state early) second-request (clock 8.11 115))
        before (quantization/tick (:state late) (assoc (clock 8.24 162) :bpm 180))
        tick (quantization/tick (:state before) (assoc (clock 8.26 172) :bpm 180))
        admission-clock (assoc (clock 8.27 176) :bpm 180)
        add-cue (fn [show decision]
                  (model/apply-command show (assoc (:command decision) :time-ms (:time-ms admission-clock))))
        apply-decisions (fn [{:keys [show queue instances receipts]} decision]
                          (let [{show :model ack :ack} (add-cue show decision)
                                fired? (= :accepted (:status ack))
                                updated (quantization/settle queue (:command-id decision) admission-clock fired?)]
                            {:show show :queue (:state updated) :instances (conj instances (:instance-id ack))
                             :receipts (conj receipts (:receipt updated))}))
        {:keys [queue instances receipts] final-show :show}
        (reduce apply-decisions {:show (assoc show :transport (select-keys admission-clock [:beat :bpm :playing?]))
                                 :queue (:state tick) :instances [] :receipts []} (:due tick))]
    (is (empty? (:instances show)))
    (is (every? empty? (map :due [early late before])))
    (is (= [:first :second] (mapv :command-id (:due tick))))
    (is (= [33/4 33/4] (mapv :due-beat receipts)))
    (is (= [0 1] (mapv #(get-in final-show [:instances % :order]) instances)))
    (is (= [176 176] (mapv #(get-in final-show [:instances % :started-at-ms]) instances)))
    (is (= [8.27 8.27] (mapv #(get-in final-show [:instances % :started-at-beat]) instances)))
    (is (= {:raw {:beat 8.04 :time-ms 89}
            :requested-at {:beat 8.08 :time-ms 100}
            :dispatched-at {:beat 8.26 :time-ms 172}
            :admitted-at {:beat 8.27 :time-ms 176}
            :status :fired}
           (select-keys (first receipts) [:raw :requested-at :dispatched-at :admitted-at :status])))
    (is (empty? (:due (quantization/tick queue admission-clock))))
    (is (= (first receipts) (:receipt (quantization/admit queue first-request admission-clock))))
    (is (= (first receipts) (:receipt (quantization/settle queue :first admission-clock false))))))

(deftest release-and-stop-before-due
  (let [initial (quantization/new-state)
        request (assoc-in (launch :held {:beats 1}) [:command :launch :mode] :held)
        held (quantization/admit initial request (clock 3.5 10))
        persistent (quantization/admit (:state held) (launch :persistent {:beats 1}) (clock 3.6 12))
        boundary (clock 4 1000)
        stopped (quantization/tick (:state persistent) (assoc boundary :playing? false))
        released (quantization/cancel (:state stopped) :held 0 :held-release)
        resumed (quantization/tick (:state released) boundary)]
    (is (empty? (:due stopped)))
    (is (= :cancelled (get-in released [:receipt :status])))
    (is (= :not-held (get-in (quantization/cancel (:state released) :persistent 0 :held-release) [:receipt :reason])))
    (is (= [:persistent] (mapv :command-id (:due resumed))))
    (is (= :cancelled (get-in (quantization/admit (:state resumed) request boundary) [:receipt :status])))
    (is (= :due (get-in (quantization/cancel (:state resumed) :persistent 0 :operator-cancel) [:receipt :status])))))

(deftest seek-and-source-replacement-invalidate-due-and-pending
  (let [initial (quantization/new-state)
        before (clock 3.5 12)
        submitted (quantization/admit initial (launch :queued {:beats 1}) before)
        immediate (quantization/admit (:state submitted) (launch :immediate :off) before)
        invalidated (quantization/invalidate (:state immediate) 0 :seek)
        queue (:state invalidated)
        after (assoc (clock 4 50) :clock-epoch 1)
        new-intent (quantization/admit queue (launch :fresh {:beats 1}) after)
        reselected (quantization/invalidate (:state new-intent) 1 :source-changed)]
    (is (= [[:queued :missed :seek] [:immediate :missed :seek]]
           (mapv (juxt :command-id :status :reason) (:missed invalidated))))
    (is (= {:state queue :due [] :reason :stale-clock-epoch} (quantization/tick queue before)))
    (is (= :stale-clock-epoch (get-in (quantization/admit queue (launch :obsolete :off) before) [:receipt :reason])))
    (is (= :stale-clock-epoch (get-in (quantization/settle queue :immediate before true) [:receipt :reason])))
    (is (= :stale-clock-epoch (get-in (quantization/cancel queue :queued 0 :cancelled) [:receipt :reason])))
    (is (= :stale-clock-epoch (:reason (quantization/invalidate queue 0 :stale-seek))))
    (is (empty? (:due (quantization/tick queue after))))
    (is (= 2 (get-in reselected [:state :clock-epoch])))
    (is (= [:fresh :missed :source-changed] ((juxt :command-id :status :reason) (first (:missed reselected)))))
    (is (empty? (:due (quantization/tick (:state reselected) (assoc after :clock-epoch 2)))))))

(deftest bounded-pending-and-retry-history
  (let [initial (quantization/new-state {:pending-limit 1 :history-limit 2})
        stopped (assoc (clock 3.5 0) :playing? false)
        gridded (launch :gridded {:beats 1})
        queued (quantization/admit initial gridded stopped)
        retried (quantization/admit (:state queued) gridded (assoc stopped :time-ms 10))
        conflicting (quantization/admit (:state retried) (assoc gridded :grid {:bars 1}) stopped)
        overflow (quantization/admit (:state conflicting) (launch :overflow {:beats 1}) stopped)
        immediate (quantization/admit (:state overflow) (dissoc (launch :immediate :off) :grid) stopped)
        rejected (quantization/settle (:state immediate) :immediate stopped false)
        cancelled (quantization/cancel (:state rejected) :gridded 0 :operator-cancel)
        another (quantization/admit (:state cancelled) (launch :another :off) stopped)
        completed (quantization/settle (:state another) :another stopped true)]
    (is (:duplicate? retried))
    (is (= (:receipt queued) (:receipt retried)))
    (is (identical? (:state queued) (:state retried)))
    (is (= :command-id-conflict (get-in conflicting [:receipt :reason])))
    (is (= :queue-full (get-in overflow [:receipt :reason])))
    (is (= [:immediate] (mapv :command-id (:due immediate))))
    (is (= :off (get-in immediate [:receipt :grid])))
    (is (= [:missed :launch-rejected {:beat 3.5 :time-ms 0}]
           ((juxt :status :reason :attempted-at) (:receipt rejected))))
    (is (= :cancelled (:status (quantization/receipt (:state completed) :gridded))))
    (is (= :fired (:status (quantization/receipt (:state completed) :another))))
    (is (nil? (quantization/receipt (:state completed) :immediate)))))

(deftest invalid-requests-are-rejected-before-enqueueing
  (let [state (quantization/new-state) at (clock 3 0)]
    (doseq [grid [nil {} {:beats 0} {:ms 1} {:bars -1} {:phrases ##Inf}
                  {:beats ##NaN} {:beats 1 :bars 1} :auto]]
      (let [result (quantization/admit state (launch :invalid grid) at)]
        (is (= :invalid-grid (get-in result [:receipt :reason])) (pr-str grid))
        (is (identical? state (:state result)))))
    (is (= :invalid-clock (get-in (quantization/admit state (launch :bad {:beats 1}) (assoc at :beat ##NaN))
                                   [:receipt :reason])))
    (is (= :invalid-raw-time (get-in (quantization/admit state (assoc (launch :bad {:beats 1}) :raw {:beat ##Inf}) at)
                                      [:receipt :reason])))
    (is (= :invalid-launch-intent
           (get-in (quantization/admit state {:command {:command-id :emergency :op :blackout/set} :grid {:beats 1}} at)
                   [:receipt :reason])))))

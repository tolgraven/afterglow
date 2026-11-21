(ns afterglow.runtime.replay-test
  (:require [afterglow.control.model :as control]
            [afterglow.runtime :as runtime]
            [afterglow.runtime.engine :as engine]
            [afterglow.runtime.executor :as executor]
            [afterglow.runtime.replay :as replay]
            [afterglow.render.frame :as render]
            [afterglow.render.ir :as ir]
            [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing]])
  (:import [java.util.concurrent CountDownLatch TimeUnit]))

(def fixtures
  [{:id :left :position [0.0 1.0 0.0] :universe 1 :address 511
    :channels {:red 1 :green 2 :blue 3 :white 4} :rgbw-policy :none}
   {:id :right :position [1.0 1.0 0.0] :universe 2 :address 10
    :channels {:red 1 :green 2 :blue 3 :white 4} :rgbw-policy :none}])

(def noise
  {:id :noise :version 1 :program :seeded :seed 42 :initial-state {:frames 0 :rng 42}
   :gain 1.0 :params {:level {:type :number :default 0.8 :bounds [0.0 1.0]}}
   :release-duration-ms 50})

(defn next-seed [seed] (mod (* 48271 seed) 2147483647))

(defn compile-test-effect
  "Small portable test program using the actual typed IR, pure explicit PRNG
  state and ordinary middleware tails. This is not the Tolglow compiler."
  [definition]
  (let [plan (ir/compile-batch
              (case (:program definition)
                :solid {:color {:op :const :value [1.0 0.2 0.1]}
                        :dimmer {:op :const :value 0.25}}
                :seeded {:dimmer {:op :param :key :sample}}))]
    (fn [context]
      (let [{:keys [instance frame]} context
            state (merge (:initial-state definition) (:state context))
            seed (when (= :seeded (:program definition)) (next-seed (:rng state)))
            release (if (= :releasing (:phase instance))
                      (- 1.0 (/ (- (:time-ms frame) (:release-at-ms instance))
                                (:release-duration-ms instance))) 1.0)
            sample (when seed (* (double (/ seed 2147483647)) (:gain definition)
                                 (get-in instance [:params :level]) release))
            data (assoc (ir/evaluate-batch plan {:params {:sample sample}}
                                          (mapv :position (:fixtures frame)))
                        :target-ids (mapv :id (:fixtures frame)) :blend :replace)]
        (-> context
            (assoc :state (cond-> (update state :frames (fnil inc 0)) seed (assoc :rng seed)))
            (runtime/append-contributions [{:kind :batch :batch data}])
            ;; Keep a real ordinary tail after a typed output block.
            (update :assignments into (mapv #(hash-map :target-id (:id %) :attribute :white
                                                       :value 0.0 :blend :replace) (:fixtures frame)))
            (update :intents conj {:type :sample :instance-id (:id instance)
                                  :version (:version definition) :seed seed}))))))

(defn command
  ([id op fields] (command 0 id op fields))
  ([epoch id op fields]
   {:kind :command :command (merge {:command-id id :show-id :recorded :epoch epoch
                                    :source {:adapter :test} :op op} fields)}))

(defn at [time-ms]
  {:kind :frame :frame {:time-ms (double time-ms)}
   :clock {:time-ms (double time-ms) :beat (/ time-ms 500.0)}})

(def setup-steps
  [(command :base :registry/publish {:kind :effects :definition {:id :base :version 1 :program :solid}})
   (command :noise :registry/publish {:kind :effects :definition noise})
   (command :cue-base :cue/put {:cue {:id :base :effect-id :base :priority 0}})
   (command :cue-preserve :cue/put {:cue {:id :preserve :effect-id :noise :priority 5 :reload-policy :preserve-state}})
   (command :cue-pinned :cue/put {:cue {:id :pinned :effect-id :noise :priority 5}})
   (command :cue-restart :cue/put {:cue {:id :restart :effect-id :noise :priority 9 :reload-policy :restart}})
   (command :launch-base :cue/launch {:cue-id :base :time-ms 0.0})
   (command :launch-preserve :cue/launch {:cue-id :preserve :time-ms 0.0})
   (command :launch-pinned :cue/launch {:cue-id :pinned :time-ms 0.0})
   (command :launch-restart :cue/launch {:cue-id :restart :time-ms 0.0})])

(defn initial-show [] (control/new-show {:show-id :recorded :rig {:fixtures fixtures}}))

(defn example-steps []
  (let [adjust (command :adjust :param/set {:instance-id "0:4" :param :level :value 0.4})]
    (into setup-steps
          [(at 0)
           (command :invalid :param/set {:instance-id "0:4" :param :level :value 2.0})
           adjust adjust (at 100)
           (command :reload :registry/publish
                    {:kind :effects :definition (assoc noise :version 2 :gain 0.5 :seed 11
                                                       :initial-state {:frames 100 :rng 11})})
           (at 200)
           (command :release :instance/end {:instance-id "0:4" :time-ms 200.0})
           (at 225) (at 250)
           (command :master :master/set {:value 0.5}) (at 300)
           (command :blackout :blackout/set {:value true}) (at 350)
           (command :restart-show :show/restart {:time-ms 400.0})
           (command :stale-release :instance/end {:instance-id "0:2" :time-ms 400.0})
           (at 400)
           (command 1 :clear-blackout :blackout/set {:value false})
           (assoc (command 1 :one-shot :cue/launch
                           {:cue-id :preserve :time-ms 450.0
                            :launch {:mode :one-shot :duration-ms 100}})
                  :clock {:time-ms 450.0 :beat 0.9})
           (at 450) (at 575) (at 600)])))

(defn frame-at [recording time-ms]
  (first (filter #(= (double time-ms) (get-in % [:frame :time-ms])) (:steps recording))))

(defn error-data [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo error (ex-data error))))

(deftest recorded-control-lifecycle-and-full-render-replay-from-portable-edn
  (let [recorded (replay/record (initial-show) (example-steps) compile-test-effect
                                {:metadata {:compiler :test-ir-program :revision "fixture-v1"}})
        trace (:recording recorded)
        decoded (edn/read-string (pr-str trace))
        verified (replay/replay decoded compile-test-effect)
        reloaded (:expected (frame-at trace 200))
        tail (:expected (frame-at trace 225))
        done (:expected (frame-at trace 250))]
    (is (= trace decoded) "No arrays/functions/custom readers are needed")
    (is (= (select-keys recorded [:model :output]) (select-keys verified [:model :output])))
    (is (= (count (example-steps)) (:verified-steps verified)))
    (is (= ["0:1" "0:2" "0:3" "0:4"]
           (mapv :instance-id (get-in (frame-at trace 0) [:expected :intents]))))
    (is (= [2 1 2] (mapv #(get-in reloaded [:instances % :effect-version]) ["0:2" "0:3" "0:4"])))
    (is (= [3 3 101] (mapv #(get-in reloaded [:instances % :state :frames]) ["0:2" "0:3" "0:4"])))
    (is (= [0.0 0.0 200.0] (mapv #(get-in reloaded [:instances % :started-at-ms]) ["0:2" "0:3" "0:4"])))
    (is (= [:effect/reloaded :effect/reloaded]
           (mapv :type (filter #(= :effect/reloaded (:type %)) (:intents reloaded)))))
    (is (= :releasing (get-in tail [:instances "0:4" :phase])))
    (is (not (contains? (:instances done) "0:4")))
    (is (= :stale-epoch (->> (:steps trace) (filter #(= :stale-release (get-in % [:command :command-id])))
                                            first :expected :ack :code)))
    (is (= 1 (get-in verified [:model :epoch])))
    (is (empty? (get-in verified [:model :instances])))
    (is (= [1 2] (vec (keys (get-in verified [:output :universes])))))
    (is (every? zero? (mapcat val (get-in verified [:output :universes]))))
    (is (= 32 (count (:steps trace))))
    (is (= :rejected (get-in trace [:steps 11 :expected :ack :status])))
    (is (= [] (get-in trace [:steps 13 :expected :events])) "Duplicate command emits no second event")
    (is (= (get-in trace [:steps 12 :expected :model-digest])
           (get-in trace [:steps 13 :expected :model-digest])))
    (is (= 550.0 (get-in (frame-at trace 575) [:expected :instances "1:1" :release-at-ms])))
    (is (= 0.9 (get-in (frame-at trace 575) [:expected :instances "1:1" :started-at-beat])))))

(deftest serial-and-real-worker-completion-reversal-replay-identically
  (let [recorded (replay/record (initial-show) (example-steps) compile-test-effect)
        trace (:recording recorded)]
    (with-open [^java.io.Closeable pool (executor/create {:workers 2 :queue-size 4 :timeout-ms 3000})]
      (let [normal (executor/mapper pool)
            reversed (fn [f instances]
                       (let [second-complete (CountDownLatch. 1)
                             first-id (:id (first instances))
                             second-id (:id (second instances))]
                         (normal (fn [instance]
                                   (when (and second-id (= first-id (:id instance)))
                                     (when-not (.await second-complete 2 TimeUnit/SECONDS)
                                       (throw (ex-info "Second effect did not finish" {}))))
                                   (let [result (f instance)]
                                     (when (= second-id (:id instance)) (.countDown second-complete))
                                     result)) instances)))
            serial (replay/replay trace compile-test-effect)
            parallel (replay/replay trace compile-test-effect {:map-work reversed})]
        (is (= serial parallel))
        (is (= trace (:recording (replay/record (initial-show) (example-steps) compile-test-effect
                                                {:map-work reversed}))))))))

(deftest priority-has-an-independent-byte-expectation
  (let [steps (conj setup-steps (at 0) (at 100))
        first-frame (replay/record (initial-show) steps compile-test-effect)
        expected (long (Math/round (* 255.0 0.8 (double (/ (next-seed (next-seed 42)) 2147483647)))))
        stronger (assoc-in steps [9 :command :launch :params :level] 0.2)
        result (replay/record (initial-show) stronger compile-test-effect)]
    (is (= expected (get-in first-frame [:output :universes 1 510])))
    (is (= (long (Math/round (* 255.0 0.2 (double (/ (next-seed (next-seed 42)) 2147483647)))))
           (get-in result [:output :universes 1 510])))
    (is (not= (get-in first-frame [:output :values :left :emitted-color])
              (get-in result [:output :values :left :emitted-color])))))

(deftest first-divergence-identifies-render-and-state-changes
  (let [trace (:recording (replay/record (initial-show) (conj setup-steps (at 0)) compile-test-effect))
        changed-renderer (fn [model frame contributions previous]
                           (replay/render-output (assoc model :master 0.0) frame contributions previous))
        render-error (error-data #(replay/replay trace compile-test-effect {:render-output changed-renderer}))
        state-error (error-data #(replay/replay trace
                                              (fn [definition]
                                                (comp (fn [context] (assoc-in context [:state :extra] true))
                                                      (compile-test-effect definition)))))
        corrupt (assoc-in trace [:initial :model :master] 0.0)]
    (is (= ::replay/mismatch (:type render-error)))
    (is (= 10 (:step-index render-error)))
    (is (= [:output-digest] (:fields render-error)))
    (is (= #{:instances :model-digest} (set (:fields state-error))))
    (is (= ::replay/invalid-recording (:type (error-data #(replay/replay corrupt compile-test-effect)))))))

(deftest appending-an-observation-never-evaluates-again-and-detaches-buffers
  (let [prepared (:model (replay/record (initial-show) setup-steps compile-test-effect))
        recording (replay/new-recording prepared)
        input (at 0)
        evaluated (engine/advance (update prepared :transport assoc :time-ms 0.0 :beat 0.0)
                                   {:time-ms 0.0 :fixtures fixtures} compile-test-effect)
        rendered (replay/render-output (:model evaluated) {:fixtures fixtures} (:contributions evaluated) nil)
        appended (replay/append-observation recording input evaluated rendered)
        digest-before (replay/digest appended)]
    (is (= 1 (count (:steps appended))))
    (is (= 1 (get-in appended [:steps 0 :expected :instances "0:4" :state :frames])))
    ;; Mutation here probes ownership after copying, not supported renderer use.
    (aset-byte ^bytes (get-in rendered [:universes 1]) 510 (byte 0))
    (aset-double ^doubles (get-in rendered [:compact :fields :intensity :values]) 0 0.0)
    (is (= digest-before (replay/digest appended)))
    (is (= (:model evaluated) (:model (replay/replay appended compile-test-effect))))))

(deftest initial-movement-history-survives-recording-and-compact-array-projection
  (let [head {:id :head :position [0 0 0] :universe 1 :address 1
              :calibration {:pan {:min-deg -540 :max-deg 540}}
              :channels {:pan [1 2] :tilt 3 :dimmer 4}}
        definition {:id :aim :version 1}
        model (control/new-show
               {:rig {:fixtures [head]}
                :registry {:effects {:aim definition}}
                :instances {"0:1" {:id "0:1" :definition definition :effect-id :aim :effect-version 1
                                   :params {} :state {} :priority 0 :order 0 :started-at-ms 0 :phase :running}}})
        previous (render/resolve-frame [head] [{:target-id :head :attribute :pan :value 0.99}]
                                       {:include-values? false :compact-values? true})
        compiler (fn [_] #(update % :assignments conj {:target-id :head :attribute :direction :value [0 0 1]}))
        recorded (replay/record model [{:kind :frame :frame {:time-ms 1.0}}] compiler {:initial-output previous})
        verified (replay/replay (edn/read-string (pr-str (:recording recorded))) compiler)
        without-history (replay/record model [{:kind :frame :frame {:time-ms 1.0}}] compiler)]
    (is (= (:output recorded) (:output verified)))
    (is (not= (:output recorded) (:output without-history)))
    (is (= 0.99 (get-in recorded [:recording :initial :output :values :head :pan])))))

(deftest canonical-digests-are-portable-and-reject-hidden-state
  (is (= (replay/digest (array-map :z #{1 2 3} :a [1/3 1M "text"]))
         (replay/digest (array-map :a [1/3 1M "text"] :z #{3 2 1}))))
  (is (not= (replay/digest [1 2]) (replay/digest '(1 2))))
  (is (= (replay/digest {:nested [1 2 3]})
         (binding [*print-length* 1 *print-level* 1 *print-meta* true]
           (replay/digest {:nested [1 2 3]}))))
  (doseq [hidden [(atom {}) (double-array [1.0]) (fn [] nil) Double/NaN Double/POSITIVE_INFINITY]]
    (is (= ::replay/nonportable
           (:type (error-data #(replay/new-recording (assoc (initial-show) :hidden hidden)))))))
  (let [recording (replay/new-recording (assoc (initial-show) :value (float 0.1)))]
    (is (= recording (edn/read-string (pr-str recording))))))

(deftest failures-and-invalid-inputs-return-no-partial-recording
  (let [model (:model (replay/record (initial-show) setup-steps compile-test-effect))
        original (replay/digest model)
        error (error-data #(replay/record model [(at 0)]
                                         (fn [_] (fn [_] (throw (ex-info "Bad effect" {:failure :effect}))))))]
    (is (= ::replay/step-failed (:type error)))
    (is (= 0 (:step-index error)))
    (is (= ::runtime/step-failed (get-in error [:cause-data :type])))
    (is (= "0:1" (get-in error [:cause-data :effect-id])))
    (is (= original (replay/digest model)))
    (doseq [input [{:kind :wrong :frame {}}
                  {:kind :frame :frame {} :command {}}
                  {:kind :frame :frame {:time-ms 0} :unexpected :field}]]
      (is (= ::replay/invalid-step (:type (error-data #(replay/record model [input] compile-test-effect))))))
    (is (= ::replay/invalid-clock
           (get-in (error-data #(replay/record model [(assoc (at 1) :clock {:time-ms 2 :beat 0.0})]
                                               compile-test-effect)) [:cause-data :type])))
    (is (= ::engine/stale-epoch
           (get-in (error-data #(replay/record model [{:kind :frame :frame {:time-ms 1 :epoch 99}}]
                                               compile-test-effect)) [:cause-data :type])))))

(deftest checked-in-recording-is-a-stable-new-runtime-regression-gate
  (let [{:keys [recording expected-bytes]} (edn/read-string
                                           (slurp (io/resource "afterglow/runtime/replay_fixture.edn")))
        result (replay/replay recording compile-test-effect)]
    (is (= 36 (:verified-steps result)))
    (is (= :test-ir-program-v1 (get-in recording [:metadata :compiler])))
    (doseq [[universe channels] expected-bytes
            [address expected] channels]
      (is (= expected (get-in result [:output :universes universe (dec address)]))))))

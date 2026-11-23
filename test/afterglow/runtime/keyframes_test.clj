(ns afterglow.runtime.keyframes-test
  (:require [clojure.test :refer [deftest is]]
            [afterglow.control.model :as control]
            [afterglow.runtime.engine :as engine]
            [afterglow.runtime.keyframes :as kf]
            [afterglow.runtime.keyframes.storage :as storage]
            [afterglow.runtime.keyframes.values :as values]
            [afterglow.runtime.executor :as executor]
            [afterglow.runtime :as runtime]
            [afterglow.render.frame :as render]))

(defn- show [options]
  (let [defn {:id :pulse :version 1 :params {:progress {:type :number :bounds [0 1] :default 0.0}}
              :keyframes options}
        registry {:effects {:pulse defn} :cues {:a {:id :a :version 1 :effect-id :pulse}}}
        model (control/new-show {:registry registry})]
    (:model (control/apply-command model {:op :cue/launch :cue-id :a :time-ms 0 :source :test :command-id "launch"
                                         :show-id (:show-id model) :epoch (:epoch model)}))))

(defn- compile-recorder [calls]
  (fn [_]
    (kf/predictable
     (fn [{:keys [frame] :as ctx}]
       (swap! calls conj [(get-in frame [:transport :beat]) (:time-ms frame)])
       (assoc ctx :assignments [{:target-id :lamp :attribute :dimmer :value (/ (:beat frame) 8.0)}])))))

(defn- advance [model previous compile beat]
  (engine/advance (assoc-in model [:transport :beat] beat)
                  {:time-ms (* beat 500) :keyframes (:keyframes previous)}
                  compile))

(deftest a-beat-ahead-uses-the-private-future-transport-once
  (let [calls (atom []) compile (compile-recorder calls)
        model (show {:interval {:beats 1} :curve :linear})
        first (advance model nil compile 0)
        half (advance (:model first) first compile 1/2)
        next (advance (:model half) half compile 1)]
    (is (= [[0.0 0.0] [1.0 500.0] [2.0 1000.0]] (mapv #(mapv double %) @calls)))
    (is (= 0.0625 (get-in half [:assignments 0 :value])))
    (is (= 0.125 (get-in next [:assignments 0 :value])))
    (is (= 0.5 (get-in half [:keyframes "0:1" :progress])))))

(deftest progress-may-reverse-and-remain-short-of-a-boundary
  (let [opts {:interval {:beats 1} :progress {:mode :replace :variable [:audio :bass]}}
        calls (atom []) compile (compile-recorder calls)
        tick (fn [prev beat bass]
               (advance (assoc-in (or (:model prev) (show opts)) [:variables :audio :bass] bass) prev compile beat))
        first (tick nil 0 0.5)
        forward (tick first 1/4 0.9)
        back (tick forward 1/2 0.1)
        next (tick back 1 0.2)]
    (is (= 0.0625 (get-in first [:assignments 0 :value])))
    (is (< (get-in back [:assignments 0 :value]) (get-in forward [:assignments 0 :value])))
    (is (== (get-in back [:assignments 0 :value]) (get-in next [:assignments 0 :value])))
    (is (= 3 (count @calls)))
    (is (= {:origin [0.0125] :target [0.25] :result [0.0125]}
           (select-keys (kf/inspect (get-in next [:keyframes "0:1"]) :lamp :dimmer) [:origin :target :result])))))

(deftest uncertified-and-stateful-effects-run-on-the-real-clock
  (let [model (show {:interval {:bars 1}}) calls (atom [])
        compile (fn [_] (fn [{:keys [frame] :as ctx}]
                          (swap! calls conj (:time-ms frame))
                          (-> ctx (update-in [:state :calls] (fnil inc 0))
                              (assoc :intents [{:type :heard}]))))
        first (advance model nil compile 0) next (advance (:model first) first compile 1/2)]
    (is (= [0 250N] @calls))
    (is (empty? (:keyframes next)))
    (is (= [{:type :heard}] (:intents next)))
    (is (= 2 (get-in next [:model :instances "0:1" :state :calls])))))

(deftest live-and-predictive-costs-are-reported-only-for-real-work
  (let [model (show {:interval {:beats 1}}) calls (atom []) observations (atom [])
        compile (compile-recorder calls)
        timed (fn [previous beat]
                (engine/advance (assoc-in (or (:model previous) model) [:transport :beat] beat)
                                {:time-ms (* 500 beat) :keyframes (:keyframes previous)
                                 :keyframe-intervals {"0:1" {:ms 1000}}
                                 :measure-effect (fn [id eligible? f] (swap! observations conj [id eligible?]) (f))}
                                compile))
        first (timed nil 0) partial (timed first 1/2) end (timed partial 2)]
    (is (= 1000 (get-in first [:keyframes "0:1" :span])))
    (is (= [["0:1" true] ["0:1" true] ["0:1" true]] @observations))
    (is (= 0.25 (get-in end [:assignments 0 :value])))))

(defn- typed-step [{:keys [frame] :as ctx}]
  (let [beat (double (:beat frame))]
    (runtime/append-contributions
     ctx [{:kind :batch :batch {:target-ids [:one :two] :blend :replace :count 2
                                :outputs {:dimmer {:components 1 :type :number
                                                   :values (double-array [(/ beat 4.0) (/ beat 2.0)])}}}}])))

(deftest typed-keyframes-retain-exact-native-dmx-and-survive-binary-detachment
  (let [fixtures [{:id :one :universe 1 :address 1 :channels {:dimmer 1}}
                  {:id :two :universe 1 :address 2 :channels {:dimmer 1}}]
        compile (constantly (kf/predictable typed-step))
        model (show {:interval {:beats 1}})
        run (fn [model frames beat mapper]
              (engine/advance (assoc-in model [:transport :beat] beat)
                              {:time-ms (* beat 500) :fixtures fixtures :keyframes frames} compile mapper))
        direct (run model nil 0 mapv) checkpoint (get-in direct [:keyframes "0:1"])
        saved (storage/freeze checkpoint)
        restored (storage/restore saved fixtures (:epoch model))]
    (with-open [pool (executor/create {:workers 2 :timeout-ms 5000})]
      (let [half (run (:model direct) {"0:1" restored} 1/2 (executor/mapper pool))
            output (render/resolve-contributions (render/compile-patch fixtures) (:contributions half) {})]
        (is (= [32 64] (mapv #(bit-and 255 %) (take 2 (get-in output [:universes 1])))))
        (is (= [0.125] (:result (kf/inspect (get-in half [:keyframes "0:1"]) :one :dimmer))))
        (is (= [0.0] (:result (kf/inspect checkpoint :one :dimmer))))))
    (is (bytes? (get-in saved [:origin 0 :batch :outputs :dimmer :values])))
    (is (thrown? clojure.lang.ExceptionInfo
                 (storage/restore (assoc-in saved [:target 0 :batch :outputs :dimmer :values] (byte-array 7)) fixtures 1)))))

(deftest changes-to-tempo-and-epoch-discard-the-old-prediction
  (let [compile (compile-recorder (atom [])) model (show {:interval {:bars 1}})
        first (advance model nil compile 0)
        slower (engine/advance (assoc (:model first) :transport {:bpm 60 :beat 1/2 :playing? true})
                               {:time-ms 250 :keyframes (:keyframes first)} compile)]
    (is (= 4250.0 (get-in slower [:keyframes "0:1" :target-clock :time-ms])))
    (is (= 0.0 (get-in slower [:assignments 0 :value])))
    (is (empty? (:keyframes (advance (assoc (:model first) :instances {}) first compile 1))))))

(deftest speculative-errors-only-quarantine-on-the-real-failing-frame
  (let [compile (constantly (kf/predictable
                             (fn [{:keys [frame] :as ctx}]
                               (when (>= (:beat frame) 1) (throw (ex-info "Bad at beat one" {})))
                               (assoc ctx :assignments [{:target-id :lamp :attribute :dimmer :value (:beat frame)}]))))
        model (show {:interval {:beats 1}})
        first (advance model nil compile 0)
        half (advance (:model first) first compile 1/2)
        failed (advance (:model half) half compile 1)]
    (is (true? (get-in first [:keyframes "0:1" :forecast-failed?])))
    (is (nil? (storage/freeze (get-in first [:keyframes "0:1"]))))
    (is (== 0.5 (get-in half [:assignments 0 :value])))
    (is (empty? (get-in half [:model :variables :runtime :events])))
    (is (some #(= "Bad at beat one" (:message %)) (get-in failed [:model :variables :runtime :events])))
    (is (empty? (:assignments failed)))))

(deftest changing-adaptive-cadence-and-missing-a-beat-preserve-linear-time
  (let [model (show nil) compile (compile-recorder (atom []))
        tick (fn [previous beat interval]
               (engine/advance (assoc-in (or (:model previous) model) [:transport :beat] beat)
                               {:time-ms (* 500 beat) :keyframes (:keyframes previous)
                                :keyframe-intervals {"0:1" interval}} compile))
        fast (tick nil 0 {:ms 100}) middle (tick fast 1/20 {:ms 100})
        slow (tick middle 1/10 {:ms 250}) progress (tick slow 3/20 {:ms 250})
        late (tick progress 9/10 {:ms 250})]
    (is (== (/ 0.1 8) (get-in slow [:assignments 0 :value])))
    (is (< (abs (- (/ 0.15 8) (get-in progress [:assignments 0 :value]))) 1.0e-15))
    (is (== (/ 0.9 8) (get-in late [:assignments 0 :value])))
    (is (== 550 (get-in late [:keyframes "0:1" :end])))))

(deftest invalid-future-columns-fall-back-through-the-current-frame
  (let [compile (constantly (kf/predictable
                             (fn [ctx]
                               (let [ctx (typed-step ctx)]
                                 (if (< (get-in ctx [:frame :beat]) 1) ctx
                                   (assoc-in ctx [:contributions 0 :batch :outputs :dimmer :values]
                                             (double-array [Double/NaN 0.0])))))))
        result (advance (show {:interval {:beats 1}}) nil compile 0)]
    (is (true? (get-in result [:keyframes "0:1" :forecast-failed?])))
    (is (= [0.0] (:result (kf/inspect (get-in result [:keyframes "0:1"]) :one :dimmer))))))

(deftest snapshot-checks-the-native-range-before-committing
  (let [result (advance (show {:interval {:beats 1}}) nil (constantly (kf/predictable typed-step)) 0)
        window (get-in result [:keyframes "0:1"])
        path [:origin 0 :batch :outputs :dimmer :values]
        checkpoint #(storage/freeze (assoc-in window path (double-array [% 0.0])))]
    (doseq [value [-0.5 1.5 Double/NaN Double/POSITIVE_INFINITY]]
      (is (thrown? clojure.lang.ExceptionInfo (storage/restore (checkpoint value) [] 0))))
    (is (some? (storage/restore (assoc-in (checkpoint 1.5) [:inputs 5] true) [] 0)))))

(deftest disabling-hdr-resamples-the-current-output-before-publication
  (let [model (show {:interval {:beats 1}})
        compile (constantly (kf/predictable
                             (fn [ctx]
                               (assoc ctx :assignments [{:target-id :lamp :attribute :dimmer
                                                         :value (if (get-in ctx [:frame :hdr?]) 1.5 0.5)}]))))
        first (engine/advance model {:time-ms 0 :hdr? true} compile)
        next (engine/advance (:model first) {:time-ms 25 :hdr? false :keyframes (:keyframes first)} compile)]
    (is (= 1.5 (get-in first [:assignments 0 :value])))
    (is (= 0.5 (get-in next [:assignments 0 :value])))))

(deftest movement-chords-crossing-the-fixture-use-its-real-curved-path
  (let [model (show {:interval {:beats 1}})
        fixtures [{:id :lamp :position [10.0 0.0 0.0]}]]
    (doseq [attr [:direction :aim] batch? [false true]]
      (let [step (fn [ctx]
                   (let [angle (* Math/PI (get-in ctx [:frame :beat]))
                         origin (if (= attr :aim) 10.0 0.0)
                         point [(+ origin (Math/cos angle)) (Math/sin angle) 0.0]]
                     (if batch?
                       (runtime/append-contributions ctx [{:kind :batch :batch {:target-ids [:lamp]
                           :outputs {attr {:type :vec3 :components 3 :values (double-array point)}}}}])
                       (assoc ctx :assignments [{:target-id :lamp :attribute attr :value point}]))))
            tick (fn [prev beat]
                   (engine/advance (assoc-in (or (:model prev) model) [:transport :beat] beat)
                                   {:time-ms (* 500 beat) :fixtures fixtures :keyframes (:keyframes prev)}
                                   (constantly (kf/predictable step))))
            first (tick nil 0) half (tick first 1/2)
            sample (kf/inspect (get-in half [:keyframes "0:1"]) :lamp attr)]
        (is (:forecast-failed? sample))
        (is (== 1.0 (get-in sample [:result 0 1])))))))

(deftest packed-aim-and-direction-check-every-head-in-its-own-coordinate-space
  (let [fixtures [{:id :left :position [0 2 0]} {:id :right :position [5 0 0]}]
        make-column (fn [a b] {:type :vec3 :components 3 :values (double-array (concat a b))})
        fields (fn [aim direction]
                 [{:kind :batch :batch {:target-ids [:left :right]
                    :outputs {:aim (make-column [1 2 0] aim)
                              :direction (make-column [0 1 0] direction)}}}])
        start (fields [6 0 0] [1 0 0])
        finish (fields [6 1 0] [1 1 0])
        checked (values/endpoints start finish fixtures :linear)]
    (is (identical? start (first checked)))
    (is (identical? finish (second checked)))
    (doseq [end [(fields [4 0 0] [1 1 0]) (fields [6 1 0] [-1 0 0])
                 (fields [5 0 0] [1 1 0]) (fields [6 1 0] [0 0 0])]]
      (is (thrown? clojure.lang.ExceptionInfo (values/endpoints start end fixtures :linear))))
    (let [collinear (fields [7 0 0] [1 0 0])]
      (is (= [start collinear] (values/endpoints start collinear fixtures :linear)))
      (is (thrown? clojure.lang.ExceptionInfo (values/endpoints start collinear fixtures :spring))))))

(defn- traced-model []
  (let [opts {:interval {:beats 1} :progress {:mode :replace :param :progress}}]
    (-> (show opts)
        (assoc-in [:instances "0:1" :definition :blocks]
                  {[:variables :weather :amount] {:stages []}
                   [:outputs :dimmer] {:stages [{:block :signed}]}})
        (assoc-in [:instances "0:1" :params :progress] 0.5))))

(defn- observed-step [sampled inspected]
  (kf/predictable
   (fn [{:keys [frame instance] :as ctx}]
     (let [beat (double (:beat frame))
           base (+ 0.3 (* 0.1 (Math/sin beat)))
           offset (get-in frame [:variables :weather :amount] -0.15)
           final (+ base offset)]
       (swap! sampled inc)
       (when (or (:keyframes frame) (::runtime/observe (meta instance)))
         (throw (ex-info "A new endpoint retained an earlier observation" {})))
       (-> ctx
           (assoc :assignments [{:target-id :lamp :attribute :dimmer :value final}])
           (vary-meta assoc ::runtime/observe
                      (fn [[path target]]
                        (swap! inspected inc)
                        (when (and (= [:outputs :dimmer] path) (= :lamp target))
                          {:base base :stages [{:block :signed :offset offset :value final}] :result final}))))))))

(defn- inspect-block [result]
  (runtime/observe (get-in result [:model :instances "0:1"]) [[:outputs :dimmer] :lamp]))

(deftest keyframed-observation-keeps-real-traces-and-only-the-displayed-native-write
  (let [sampled (atom 0) reads (atom 0) compile (constantly (observed-step sampled reads))
        initial (advance (traced-model) nil compile 0)
        half (advance (:model initial) initial compile 1/2)
        window (get-in half [:keyframes "0:1"])
        _ (is (zero? @reads))
        {:keys [keyframe result stages time-ms]} (inspect-block half)
        at-boundary (advance (:model half) half compile 1)
        next (inspect-block at-boundary)]
    (is (= 3 @sampled))
    (is (= 250.0 (double time-ms)))
    (is (= :target (:trace-source keyframe)))
    (is (= [0.5 1.0] (mapv double [(:progress keyframe) (get-in keyframe [:sample-clock :beat])])))
    (is (= -0.15 (:offset (first stages))))
    (is (= [result] (get-in keyframe [:native :target])))
    (is (= (get-in half [:assignments 0 :value]) (get-in keyframe [:native :result 0])))
    (is (not= result (get-in keyframe [:native :result 0])))
    (is (= 0.3 (get-in keyframe [:origin-trace :base])))
    (is (= :interpolated (get-in next [:keyframe :origin-kind])))
    (is (nil? (get-in next [:keyframe :origin-trace])))
    (is (= (get-in half [:assignments 0 :value]) (get-in next [:keyframe :native :origin 0])))
    (let [saved (storage/freeze window) restored (storage/restore saved (:rig window) (:epoch window))
          resumed (advance (:model half) {:keyframes {"0:1" restored}} compile 3/4)]
      (is (nil? (meta (:origin saved))))
      (is (nil? (inspect-block resumed)))
      (is (= 3 @sampled)))))

(deftest variable-bindings-invalidate-forecasts-on-resolved-leaf-changes
  (let [sampled (atom 0) reads (atom 0) compile (constantly (observed-step sampled reads))
        tick (fn [prev beat amount other]
               (engine/advance (assoc-in (or (:model prev) (traced-model)) [:transport :beat] beat)
                               {:time-ms (* 500 beat) :keyframes (:keyframes prev)
                                :resolved-variables {:weather {:amount amount :other other}}} compile))
        first (tick nil 0 0.1 1)
        stable (tick first 1/4 0.1 2)
        _ (is (= 2 @sampled))
        changed (tick stable 1/2 -0.1 3)
        trace (inspect-block changed)]
    (is (= 4 @sampled))
    (is (= -0.1 (get-in trace [:stages 0 :offset])))
    (is (= -0.1 (get-in trace [:keyframe :origin-trace :stages 0 :offset])))
    (is (== 1.5 (get-in trace [:keyframe :target-clock :beat])))))

(defn- variable-source-step [sampled reads path]
  (let [step (vary-meta (observed-step sampled reads) assoc ::kf/variable-paths [path])
        add-source (fn [{:keys [frame] :as ctx}]
                     (update-in ctx [:frame :variables :weather :amount] + (get-in frame path 0.0)))]
    (kf/with-inputs step add-source)))

(deftest compiled-variable-paths-and-direct-bindings-share-a-forecast
  (let [sampled (atom 0) reads (atom 0)
        compile (constantly (variable-source-step sampled reads [:variables :rack "booth" 0]))
        tick (fn [prev beat direct source other]
               (engine/advance (assoc-in (or (:model prev) (traced-model)) [:transport :beat] beat)
                               {:time-ms (* 500 beat) :keyframes (:keyframes prev)
                                :resolved-variables {:weather {:amount direct} :rack {"booth" [source other]}}}
                               compile))
        initial (tick nil 0 0.1 0.1 1)
        stable (tick initial 1/4 0.1 0.1 2)
        target #(get-in % [:keyframes "0:1" :target])]
    (is (= 2 @sampled))
    (is (identical? (target initial) (target stable)))
    (is (zero? @reads))
    (is (= 0.2 (get-in (inspect-block stable) [:stages 0 :offset])))
    (let [window (get-in stable [:keyframes "0:1"])
          restored (storage/restore (storage/freeze window) (:rig window) (:epoch window))
          resumed (tick (assoc-in stable [:keyframes "0:1"] restored) 3/8 0.1 0.1 3)
          _ (is (= 2 @sampled))
          changed (tick resumed 1/2 0.1 -0.1 2)
          trace (inspect-block changed)]
      (is (= 4 @sampled))
      (is (not (identical? (target stable) (target changed))))
      (is (zero? (get-in trace [:keyframe :origin-trace :stages 0 :offset])))
      (is (zero? (get-in trace [:stages 0 :offset])))
      (is (== 1.5 (get-in trace [:keyframe :target-clock :beat])))
      (let [direct-changed (tick changed 3/4 -0.1 -0.1 2)]
        (is (= 6 @sampled))
        (is (= -0.2 (get-in (inspect-block direct-changed) [:keyframe :origin-trace :stages 0 :offset])))))))

(deftest compiled-variable-values-distinguish-absent-from-present-nil
  (let [path [:variables :optional]
        step (fn [{:keys [frame] :as ctx}]
               (let [value (if (nil? (get-in frame path :absent)) 0.2 0.6)]
                 (assoc ctx :assignments [{:target-id :lamp :attribute :dimmer :value value}])))
        compile (constantly (vary-meta (kf/predictable step) assoc ::kf/variable-paths #{path}))
        initial (advance (show {:interval {:beats 1}}) nil compile 0)
        present (advance (assoc-in (:model initial) path nil) initial compile 1/4)
        removed (advance (update (:model present) :variables dissoc :optional) present compile 1/2)]
    (is (= [0.6 0.2 0.6] (mapv #(get-in % [:assignments 0 :value]) [initial present removed])))))

(deftest first-inspection-after-many-partial-retargets-runs-one-endpoint-reader
  (let [sampled (atom 0) inspected (atom 0)
        compile (constantly (observed-step sampled inspected))
        result (reduce (fn [previous beat] (advance (or (:model previous) (traced-model)) previous compile beat))
                       nil (range 100))]
    (is (zero? @inspected))
    (is (= :interpolated (get-in (inspect-block result) [:keyframe :origin-kind])))
    (is (= 1 @inspected))
    (is (= 101 @sampled))))

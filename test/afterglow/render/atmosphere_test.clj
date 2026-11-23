(ns afterglow.render.atmosphere-test
  (:require [afterglow.render.atmosphere :as fog]
            [afterglow.render.frame :as frame]
            [afterglow.render.blocks :as blocks]
            [afterglow.render.fog-optics :as optics]
            [afterglow.render.ir :as ir]
            [clojure.test :refer [deftest is]]))

(def fixture {:id :jet :position [1 2 3] :universe 4 :address 512 :channels {:fog [1 2]}
              :fogger {:flow-m3-min 60 :direction [0 0 -2] :mixing-seconds 4}})
(def room {:width 10 :height 4 :depth 5 :fog-half-life-s 60 :air-changes-per-hour 3})
(def plan (fog/plan room (frame/compile-patch [fixture])))
(def full {4 (assoc (vec (repeat 512 0)) 511 -1) 5 [0]})
(def off {4 (vec (repeat 512 0)) 5 [0]})
(defn near? [a b] (< (abs (- a b)) 1e-8))
(defn total [s] (+ (:mixed-m3 s) (reduce + 0 (map :local-m3 (:sources s)))))

(deftest split-universe-controls-hold-each-byte-independently
  (let [s (fog/initial plan 0 0)
        high {4 (assoc (vec (repeat 512 0)) 511 120)}
        send #(fog/present plan %1 %2 %3)
        a (send s 1000 high)
        b (send a 2000 {5 [128]})
        c (send b 3000 {4 (vec (repeat 512 0))})
        flow #(get-in % [:sources 0 :flow-m3-s])]
    (is (near? (/ 120 255) (flow a)))
    (is (near? (/ (+ 120 (/ 128 255)) 255) (flow b)))
    (is (near? (/ 128 (* 255 255)) (flow c)))
    (is (near? (+ (flow a) (flow b)) (get-in c [:sources 0 :emitted-m3])))
    (is (= (:sources c) (:sources (send c 3000 {6 [0]}))))))

(deftest flow-is-applied-to-the-correct-interval-and-diffuses-after-switch-off
  (let [s (fog/initial plan 2 0)
        on (fog/present plan s 500 full)
        mid (fog/present plan on 2500 full)
        stop (fog/present plan mid 4500 off)
        late (fog/advance plan stop 8500)
        once (fog/present plan on 4500 off)
        details (first (:sources late))]
    (is (zero? (total on)))
    (is (= [0.0 0.0 -1.0] (:direction details)))
    (is (= 4.0 (:emitted-m3 details)))
    (is (< 0 (total late) (total stop) 4))
    (is (< (:mixed-m3 stop) (:mixed-m3 late)))
    (is (near? (total stop) (total once)))
    (is (near? (get-in stop [:sources 0 :local-m3]) (get-in once [:sources 0 :local-m3])))
    (is (near? (/ (:mixed-m3 late) 200) (:mixed-density late)))
    (is (thrown? Exception (fog/advance plan late 8499)))
    (is (near? (total late) (total (fog/reconfigure (assoc plan :sources []) late 3 123 true))))))
(deftest sightline-rate-follows-mixing-and-total-room-clearance
  (let [measured (assoc room :measured-fog {:clearance-half-life-s 12.0 :reference-path-m 3})
        calibrated (fog/plan measured (frame/compile-patch [fixture]))
        clear (fog/initial calibrated 0 0)
        start (fog/present calibrated clear 0 full)
        stop (fog/present calibrated start 4000 off)
        late (fog/advance calibrated stop 49000)]
    (is (= 0.0 (:fog-level-change-per-s clear)))
    (is (near? 12.0 (:clearance-half-life-s clear)))
    (is (< (:clearance-half-life-s (fog/initial plan 0 0)) 60))
    (is (pos? (:fog-level-change-per-s stop)) "A stopped nozzle can still thicken the haze")
    (is (neg? (:fog-level-change-per-s late)))
    (doseq [sample [stop late]]
      (let [ms (:sample-time-ms sample)
            after (fog/advance calibrated sample (+ ms 0.001))
            numerical-rate (* 1.0e6 (- (:fog-level after) (:fog-level sample)))]
        (is (near? numerical-rate (:fog-level-change-per-s sample)))))))

(deftest partial-dmx-range-reversed-address-and-finite-fog-validation
  (let [plan (fog/plan room (frame/compile-patch [(assoc-in fixture [:fogger :dmx-range] [240 40])]))
        s (fog/initial plan 0 0)
        on (fog/present plan s 0 {4 (assoc (vec (repeat 512 0)) 511 140) 5 [0]})]
    (is (= 0.5 (get-in on [:sources 0 :flow-m3-s])))
    (is (= 0.5 (get-in (fog/present plan on 1000 {7 [0]}) [:sources 0 :flow-m3-s])))
    (is (thrown? Exception (fog/validate-fogger! (assoc-in fixture [:fogger :flow-m3-min] -1))))
    (is (thrown? Exception (fog/plan (assoc room :fog-half-life-s 0) (frame/compile-patch [fixture]))))))

(deftest calibrated-fog-idles-at-its-physical-off-bytes
  (doseq [[off pivot] [[255 0] [224.5 42] [128 41.3] [255 30.1] [201.25 nil]]]
    (let [f (-> fixture (assoc-in [:fogger :dmx-range] [off 1])
                (assoc-in [:channels :fog] (cond-> {:offset 1 :fine-offset 2} pivot (assoc :inverted-from pivot))))
          patch (frame/compile-patch [f]) nozzle (first (:fixtures patch))
          channel (get-in nozzle [:compiled-channels :fog])
          level (fog/physical-level channel 85.5)
          raw [{:target-id :jet :attribute :fog :value level}]
          read-bytes (fn [packet] (mapv #(bit-and 255 (get-in packet %)) [[4 511] [5 0]]))
          off-pair [(int off) (Math/round (* 255.0 (- off (int off))))]
          run (fn [rows options] (:universes (frame/resolve-frame patch rows options)))]
      (is (= (zipmap [[4 511] [5 0]] off-pair) (fog/off-bytes nozzle)))
      (is (= off-pair (read-bytes (frame/idle-universes patch))))
      (doseq [options [{} {:include-values? false} {:include-values? false :compact-values? true}]]
        (is (= [85 128] (read-bytes (run raw options))))
        (is (= off-pair (read-bytes (run [] options))))
        (is (= off-pair (read-bytes (run raw (assoc options :blackout? true)))))
        (is (= off-pair (read-bytes (run raw (assoc options :master 0)))))
        (is (= off-pair (read-bytes (run [(assoc (first raw) :opacity 0)] options)))))))
  (let [patch (frame/compile-patch [(dissoc fixture :fogger)])
        raw [{:target-id :jet :attribute :fog :value 1.0}]]
    (is (= {} (:fog-off-bytes patch)))
    (is (= 255 (bit-and 255 (get-in (frame/resolve-frame patch raw {:blackout? true}) [:universes 4 511]))))))

(deftest calibrated-endpoints-resolve-to-exact-flow-after-dmx-quantization
  (doseq [channel [1 [1 2]], endpoints [[80.6 180.2] [180.2 80.6] [80.4001 80.8]]
          :when (or (vector? channel) (not= (Math/round (double (first endpoints)))
                                             (Math/round (double (second endpoints)))))]
    (let [f (-> fixture (assoc-in [:channels :fog] channel) (assoc-in [:fogger :dmx-range] endpoints))
          patch (frame/compile-patch [f])
          nozzle (first (:fixtures patch)) channel (get-in nozzle [:compiled-channels :fog])
          plan (fog/plan room patch) start (fog/initial plan 0 0)
          idle (frame/idle-universes patch)
          full (:universes (frame/resolve-frame patch [{:target-id :jet :attribute :fog
                                                        :value (fog/physical-level channel (second endpoints))}]))
          flow #(get-in % [:sources 0 :flow-m3-s])]
      (is (zero? (flow (fog/present plan start 1 idle))))
      (when (:fine channel)
        (is (zero? (flow (fog/present plan start 1 (select-keys idle [4])))))
        (is (zero? (flow (fog/present plan start 1 (select-keys idle [5]))))))
      (is (== 1 (flow (fog/present plan start 1 full))))))
  (is (thrown? clojure.lang.ExceptionInfo
               (frame/compile-patch [(-> fixture (assoc-in [:channels :fog] 1)
                                         (assoc-in [:fogger :dmx-range] [80.1 80.2]))]))))

(deftest fractional-pivots-keep-the-requested-dmx-quantization-bin
  (let [buffers {0 (byte-array 512)}
        mismatches
        (for [pivot [nil 0 0.7001 30.1 41.3 65.04260156355254 209.678 255]
              fine [nil [0 1]]
              :let [channel {:coarse [0 0] :fine fine :inverted-from pivot}]
              value (concat [0.0 255.0 (double (or pivot 0))]
                            (for [coarse (range 255) fraction [0.0 0.3 0.5 0.9999]] (+ coarse fraction)))
              :let [level (fog/physical-level channel value)
                    expected (if fine [(int value) (Math/round (* 255.0 (- value (int value))))]
                                 [(Math/round value)])
                    _ (frame/pack-value! buffers channel level)
                    actual (mapv #(bit-and 255 (aget ^bytes (buffers 0) %)) (range (count expected)))]
              :when (not= expected actual)]
          {:pivot pivot :value value :expected expected :actual actual})]
    (is (empty? (take 1 mismatches)) (pr-str (first mismatches)))))

(deftest released-plumes-forecast-the-peak-of-the-same-coasting-model
  (let [other (-> fixture (assoc :id :slow :universe 7) (assoc-in [:fogger :mixing-seconds] 40))
        plan (fog/plan room (frame/compile-patch [fixture other]))
        state (-> (fog/initial plan 0 0) (assoc :mixed-m3 0.3)
                  (assoc-in [:sources 0 :local-m3] 0.7) (assoc-in [:sources 1 :local-m3] 2.0))
        peak (fog/coasting-peak plan state)
        sample #(:mixed-m3 (fog/advance plan state (* 1000 %)))
        t (:after-s peak)]
    (is (pos? t))
    (is (near? (:mixed-m3 peak) (sample t)))
    (is (near? (:fog-level peak) (:fog-level (fog/advance plan state (* 1000 t)))))
    (is (< (sample (dec t)) (:mixed-m3 peak)))
    (is (< (sample (inc t)) (:mixed-m3 peak)))
    (is (< (:mixed-m3 state) (:mixed-m3 peak) 3))
    (let [clear (fog/initial plan 0 0)]
      (is (= {:after-s 0.0 :mixed-m3 0.0 :fog-level 0.0} (fog/coasting-peak plan clear))))))

(deftest shared-material-and-measured-sightline
  (doseq [[extinction density distance expected]
          [[1.25 0.1 8.0 (/ 1 Math/E)]
           [2.5 0.1 8.0 (Math/exp -2)]
           [-2.5 0.1 8.0 1.0]
           [1.25 -0.1 8.0 1.0]
           [1.25 0.1 -8.0 1.0]
           [1000.0 1.0 1.0 0.0]]]
    (let [depth (optics/optical-depth extinction density distance)
          material (blocks/fog-transmission-expression extinction density distance)]
      (is (near? expected (ir/evaluate material {})))
      (is (near? expected (optics/transmittance depth)))
      (is (near? (- 1 expected) (optics/absorptance depth)))))
  ;; Local control needs the absorbed fraction even below double precision at 1.
  (let [depth (optics/optical-depth 1 1e-19 1)]
    (is (== 1.0 (optics/transmittance depth)))
    (is (== 1e-19 (optics/absorptance depth)))))

(deftest optical-depth-rejects-nonfinite-inputs-and-overflow
  (doseq [args [[##NaN 1 1] [1 ##-Inf 1] [1 1 ##Inf] [1e300 1e300 1]]]
    (is (thrown? clojure.lang.ExceptionInfo (apply optics/optical-depth args)))))

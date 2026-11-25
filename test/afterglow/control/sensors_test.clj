(ns afterglow.control.sensors-test
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.edn :as edn]
            [afterglow.control.sensors :as sensors]
            [afterglow.control.model :as model]))

(def base-config {:version 1 :channels [{:id :tilt :input :pitch}]})

(defn sample [id time beat values]
  {:version 1 :device-id "phone" :session-id "one" :sample-id id :time-ms time
   :device-time-ms time :beat beat :meter {:beats-per-bar 7/2 :bars-per-phrase 4}
   :values values :gestures []})

(defn state [& [armed?]] (sensors/new-state {:device-id "phone" :session-id "one" :armed? (boolean armed?)
                                           :meter {:beats-per-bar 7/2 :bars-per-phrase 4}}))

(defn near? [a b] (< (Math/abs (double (- a b))) 1.0e-9))

(def shot {:op :cue/launch :cue-id :flash :launch {:mode :one-shot :duration {:beats 1/8}}})

(deftest calibration-transform-pipelines-and-physical-time-filter-are-explicit
  (let [config {:version 1 :channels [{:id :tilt :input :pitch :calibrated? true :smoothing-ms 100
                                     :transforms [{:op :wrap :period (* 2 Math/PI)}
                                                  {:op :deadband :width 0.1} {:op :scale :value 2}
                                                  {:op :map-range :in [-1 1] :out [0 1]}
                                                  {:op :curve :kind :smoothstep}]}]}
        calibrated (sensors/calibrate (state) (sample 0 0 0 {:pitch 1}))
        first (sensors/step calibrated config (sample 1 0 0 {:pitch 1}))
        next (sensors/step (:state first) config (sample 2 100 0 {:pitch 1.6}))]
    (is (= {:pitch 1} (:baseline calibrated)))
    (is (== 0.5 (get-in first [:context :sensor-values :tilt])))
    (is (near? (+ 0.5 (* 0.5 (- 1 (Math/exp -1)))) (get-in next [:context :sensor-values :tilt])))
    (is (= [] (:commands next)))
    (is (thrown? clojure.lang.ExceptionInfo (sensors/calibrate (state true) (sample 0 0 0 {}))))
    (is (= -0.25 (sensors/transform 0.75 {:op :wrap :period 1})))
    (is (== 0.0 (sensors/transform -0.01 {:op :deadband :width 0.1})))
    (is (= (:state next) (edn/read-string (pr-str (:state next)))))))

(deftest missing-measurements-never-become-zero-and-derived-magnitudes-compose
  (let [config {:version 1 :channels [{:id :motion :input {:op :magnitude :inputs [:x :y :z]}}]}
        result (sensors/step (state) config (sample 1 10 0 {:x 3 :y 4 :z 0}))
        missing (sensors/step (:state result) config (sample 2 20 0 {:x 3 :y 4}))]
    (is (= 5.0 (get-in result [:context :sensor-values :motion])))
    (is (= {} (get-in missing [:context :sensor-values])))
    (is (= {} (get-in missing [:state :channels])))
    (is (thrown? clojure.lang.ExceptionInfo (sensors/step (state) config (sample 0 0 0 {:x nil}))))))

(deftest typed-bindings-produce-real-shared-reducer-commands-and-no-authority
  (let [definition {:id :light :version 1 :params {:level {:type :number :default 0 :bounds [0 1]}}}
        base (model/new-show {:registry {:effects {:light definition} :cues {:light {:id :light :effect-id :light}}}})
        launch (model/apply-command base {:op :cue/launch :cue-id :light :source :test :show-id :main :epoch 0 :command-id :launch :time-ms 0})
        config (assoc base-config :bindings [{:id :level :channel :tilt :schema (get-in definition [:params :level])
                                             :command {:op :param/set :instance-id "0:1" :param :level}}])
        sensed (sensors/step (state true) config (sample 0 0 0 {:pitch 0.7}))
        command (first (:commands sensed))
        updated (model/apply-command (:model launch) (merge command {:source :sensor :show-id :main :epoch 0 :command-id :sensor :time-ms 0}))]
    (is (= {:op :param/set :instance-id "0:1" :param :level :value 0.7} command))
    (is (= :accepted (get-in updated [:ack :status])))
    (is (= 0.7 (get-in updated [:model :instances "0:1" :params :level])))
    (is (= [] (:commands (sensors/step (:state sensed) config (sample 1 10 0 {:pitch 0.7001})))))
    (is (thrown? clojure.lang.ExceptionInfo (sensors/step (state true) config (sample 0 0 0 {:pitch 3}))))))

(deftest discrete-and-vector-parameter-bindings-use-captured-schemas
  (let [schemas {:count {:type :integer :default 1 :bounds [0 8]}
                 :on {:type :boolean :default false}
                 :shape {:type :enum :values [:a :b :c] :default :a}
                 :color {:type :color :default [0 0 0]}}
        config {:version 1 :channels [{:id :x :input :x} {:id :y :input :y} {:id :z :input :z}]
                :bindings (mapv (fn [[k schema]] (merge {:id k :schema schema
                                                         :command {:op :param/set :instance-id "0:1" :param k}}
                                                        (if (= k :color) {:channels [:x :y :z]} {:channel :x}))) schemas)}
        result (sensors/step (state true) config (sample 0 0 0 {:x 0.75 :y 0.2 :z 0.1}))]
    (is (= {:count 1 :on true :shape :c :color [0.75 0.2 0.1]}
           (into {} (map (juxt :param :value)) (:commands result))))))

(deftest hysteresis-and-musical-cooldown-dont-fire-on-noise-or-transport-pause
  (let [config (assoc base-config :triggers [{:id :flick :channel :tilt :on 2 :off 1
                                             :cooldown {:bars 1} :command shot}])
        run (fn [state id ms beat pitch] (sensors/step state config (sample id ms beat {:pitch pitch})))
        first (run (state true) 0 0 0 2)
        noise (run (:state first) 1 100 0.2 1.5)
        off (run (:state noise) 2 200 1 0.9)
        early (run (:state off) 3 300 2 2.1)
        off-again (run (:state early) 4 400 2.5 0)
        paused (run (:state off-again) 5 50000 2.5 2)
        off-final (run (:state paused) 6 50100 3.5 0)
        final (run (:state off-final) 7 50200 3.5 2)]
    (is (= [shot] (:commands first) (:commands final)))
    (is (every? empty? (map :commands [noise off early off-again paused off-final])))
    (is (= 7/2 (get-in first [:state :triggers :flick :cooldown-timer :duration :value])))))

(deftest held-cues-retain-exact-ack-ownership-through-early-release-and-disarm
  (let [config (assoc base-config :triggers [{:id :hold :channel :tilt :on 2 :off 1
                                             :command {:op :cue/launch :cue-id :wash :launch {:mode :held :params {:level 0.6}}}}])
        pressed (sensors/step (state true) config (sample 0 0 0 {:pitch 2}))
        gesture-id (-> pressed :commands first :gesture-id)
        released (sensors/step (:state pressed) config (sample 1 20 0 {:pitch 0}))
        acked (sensors/acknowledge (:state released) gesture-id {:status :accepted :instance-id "0:7"})
        again (sensors/acknowledge (:state acked) gesture-id {:status :accepted :instance-id "0:7"})]
    (is (= {:mode :held :params {:level 0.6}} (-> pressed :commands first :launch)))
    (is (= [] (:commands released)))
    (is (= [{:op :instance/end :instance-id "0:7"}] (:commands acked)))
    (is (= [] (:commands again)))
    (let [known (sensors/acknowledge (:state pressed) gesture-id {:status :accepted :instance-id "0:8"})
          disarmed (sensors/set-armed (:state known) false)]
      (is (= [{:op :instance/end :instance-id "0:8"}] (:commands disarmed)))
      (is (false? (get-in disarmed [:state :armed?])))
      (is (= [] (:commands (sensors/set-armed (:state disarmed) false)))))))

(deftest gesture-pulses-dedupe-across-packets-and-keep-semantic-not-finger-identity
  (let [config (assoc base-config :gestures [{:id :tap :type :primary-action :cooldown {:beats 1/4} :command shot}])
        packet (assoc (sample 0 0 0 {}) :gestures [{:id "tap1" :type :primary-action :phase :pulse}])
        first (sensors/step (state true) config packet)
        duplicate (sensors/step (:state first) config (assoc packet :sample-id 1 :time-ms 100 :device-time-ms 100 :beat 1))
        second (sensors/step (:state duplicate) config (assoc packet :sample-id 2 :time-ms 200 :device-time-ms 200 :beat 2
                                                            :gestures [{:id "tap2" :type :primary-action :phase :pulse}]))]
    (is (= [shot] (:commands first) (:commands second)))
    (is (= [] (:commands duplicate)))
    (is (= [:sensor/gesture] (mapv :type (:events first))))))

(deftest stale-and-wrong-source-samples-preserve-owned-state-and-values
  (let [first (sensors/step (state) base-config (sample 3 100 1 {:pitch 0.4}))]
    (doseq [packet [(sample 3 100 1 {:pitch 0.9})
                    (sample 4 99 1 {:pitch 0.9})
                    (sample 4 101 0.5 {:pitch 0.9})
                    (assoc (sample 4 101 2 {:pitch 0.9}) :device-time-ms 50)
                    (assoc (sample 4 101 2 {:pitch 0.9}) :session-id "stale")]]
      (let [result (sensors/step (:state first) base-config packet)]
        (is (identical? (:state first) (:state result)))
        (is (= {:tilt 0.4} (get-in result [:context :sensor-values])))
        (is (= [] (:commands result)))
        (is (= :sensor/sample-rejected (-> result :events clojure.core/first :type)))))))

(deftest missing-input-and-dropout-release-only-owned-holds
  (let [config (assoc base-config :timeout-ms 50 :triggers [{:id :hold :channel :tilt :on 1 :off 0 :command {:op :cue/launch :cue-id :wash :launch {:mode :held}}}])
        begun (sensors/step (state true) config (sample 0 0 0 {:pitch 2}))
        gesture-id (-> begun :commands first :gesture-id)
        acked (sensors/acknowledge (:state begun) gesture-id {:status :accepted :instance-id "2:3"})
        missing (sensors/step (:state acked) config (sample 1 10 0 {}))
        expired (sensors/expire (:state acked) config {:time-ms 51 :beat 0})]
    (is (= [{:op :instance/end :instance-id "2:3"}] (:commands missing) (:commands expired)))
    (is (= :sensor/dropout (-> expired :events last :type)))
    (is (empty? (:events (sensors/expire (:state expired) config {:time-ms 100 :beat 0}))))))

(deftest whole-context-middleware-composes-independent-sources-and-validates-intent-vectors
  (let [a (sample 0 0 0 {:pitch 0.5}) b (assoc a :device-id "watch" :values {:pitch 0.75})
        ctx {:state {:effect :private} :custom [:untouched] :commands [] :events []}
        result ((comp (sensors/middleware base-config b) (sensors/middleware base-config a)) ctx)]
    (is (= (:state ctx) (:state result)))
    (is (= [:untouched] (:custom result)))
    (is (= { ["phone" "one"] {:tilt 0.5} ["watch" "one"] {:tilt 0.75}} (:sensor-values result)))
    (is (every? false? (map :armed? (vals (:sensor-states result)))))
    (is (= [] (:commands result)))
    (is (thrown? clojure.lang.ExceptionInfo ((sensors/middleware base-config a) {:commands {}})))
    (is (thrown? clojure.lang.ExceptionInfo ((sensors/middleware base-config a) {:commands [{:op :show/restart}]})))))

(deftest configuration-and-intents-reject-ambiguous-or-authority-bearing-data
  (doseq [config [(assoc base-config :channels [{:id :x :input :pitch :smoothing-ms -1}])
                  (assoc base-config :triggers [{:id :x :channel :tilt :on 1 :off 1 :command shot}])
                  (assoc base-config :gestures [{:id :x :type :primary-action :command {:op :cue/launch :cue-id :x :launch {:mode :held}}}])
                  (assoc base-config :channels [{:id :x :input :pitch :transforms [{:op :random}]}])]]
    (is (thrown? clojure.lang.ExceptionInfo (sensors/validate-config config))))
  (doseq [command [(assoc shot :epoch 1) {:op :cue/launch :cue-id :x :launch {:mode :one-shot}}
                   {:op :instance/end} {:op :master/set :value 2} {:op :show/restart}]]
    (is (thrown? clojure.lang.ExceptionInfo (sensors/validate-command command))))
  (is (thrown? clojure.lang.ExceptionInfo (sensors/transform Double/MAX_VALUE {:op :scale :value 2}))))

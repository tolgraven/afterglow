(ns afterglow.control.devices.session-test
  (:require [clojure.test :refer [deftest is testing]]
            [afterglow.control.model :as model]
            [afterglow.control.devices.session :as session]
            [afterglow.control.devices.push-2 :as push]
            [afterglow.control.devices.generic :as generic]
            [afterglow.control.codecs.push-2 :as codec]))

(defn initial-model []
  (model/new-show
    {:registry {:effects {:wash {:id :wash :version 1 :params {:level {:type :number :default 0.5 :bounds [0 1]}}}}
                :cues {:held {:id :held :version 1 :effect-id :wash :held true :color [1 0 0]}
                       :latched {:id :latched :version 1 :effect-id :wash :color [0 0 1]}}}
     :pages {:main {:id :main :cells {[0 0] :held [1 0] :latched}}}}))

(defn harness
  ([] (harness {}))
  ([overrides]
   (let [show (atom (initial-model)) now (atom 0) log (atom []) callbacks (atom [])
         display-count (atom 0)
         midi {:open! (fn [f] (swap! callbacks conj f) (swap! log conj [:midi/open]) (Object.))
               :send! (fn [_ messages] (swap! log into (map #(vector :midi/send %) messages)))
               :close! (fn [_] (swap! log conj [:midi/close]))}
         display {:open! #(do (swap! display-count inc) (swap! log conj [:display/open]) (Object.))
                  :render! (fn [_ view] (swap! log conj [:display/render view]))
                  :close! (fn [_] (swap! log conj [:display/close]))}
         options (merge {:session-id "device-a" :model! #(deref show) :now-ms! #(deref now)
                         :dispatch! (fn [command]
                                      (locking show
                                        (swap! log conj [:command command])
                                        (let [result (model/apply-command @show command)]
                                          (reset! show (:model result)) result)))
                         :midi midi :display display :profile (push/profile {})} overrides)]
     {:show show :now now :log log :callbacks callbacks :display-count display-count
      :options options :session (session/create options)})))

(defn palette! [h index]
  ((last @(:callbacks h)) (assoc (codec/palette-write 0 index [index 0 0 31]) 6 4)))

(defn ready! [h]
  (session/open! (:session h))
  (doseq [index (range 128)] (palette! h index))
  h)

(defn led-ack! [h] ((last @(:callbacks h)) [0xf0 0 0x21 0x1d 0 1 9 100 0xf7]))

(deftest opens-explicitly-queries-palettes-in-order-and-diffs-output
  (let [h (harness) device (:session h)]
    (is (= [] @(:log h)))
    (session/open! device)
    (is (= :active (:status (session/snapshot device))))
    (is (= (codec/palette-request 0 0) (second (first (filter #(= :midi/send (first %)) @(:log h))))))
    (palette! h 5)
    (is (= {} (get-in (session/snapshot device) [:local :palettes])))
    (doseq [index (range 128)] (palette! h index))
    (is (true? (get-in (session/snapshot device) [:local :ready?])))
    (is (= 128 (count (get-in (session/snapshot device) [:local :palettes]))))
    (is (some #(= [:midi/send (codec/sysex 0 [10 1])] %) @(:log h)))
    (is (some #(= [:midi/send (codec/sysex 0 [30 1])] %) @(:log h)))
    (is (= 8 (count (get-in (session/snapshot device) [:local :last-leds]))))
    (dotimes [_ 8] (led-ack! h))
    (is (= 64 (count (get-in (session/snapshot device) [:local :last-leds]))))
    (let [before @(:log h)]
      (session/refresh! device)
      (is (= before @(:log h)) "unchanged views produce no MIDI/display sends"))
    (session/close! device)))

(deftest held-and-latching-cues-use-real-shared-model
  (let [h (ready! (harness)) receive (last @(:callbacks h)) device (:session h)]
    (receive [0x90 36 100])
    (let [id (first (keys (:instances @(:show h))))]
      (is (= :held (get-in @(:show h) [:instances id :launch-mode])))
      (is (= {:adapter :push-2 :session-id "device-a"} (get-in @(:show h) [:instances id :source])))
      (receive [0xb0 71 10])
      (is (= 0.6 (get-in @(:show h) [:instances id :params :level])))
      (receive [0x80 36 0])
      (is (= :releasing (get-in @(:show h) [:instances id :phase]))))
    (receive [0x90 37 127])
    (let [id (get-in (session/snapshot device) [:local :selected-instance])]
      (receive [0x80 37 0])
      (is (= :running (get-in @(:show h) [:instances id :phase])))
      (receive [0x90 37 127])
      (is (= :releasing (get-in @(:show h) [:instances id :phase])))
      (receive [0x90 37 127])
      (is (nil? (get-in @(:show h) [:instances id]))))
    (session/close! device)))

(deftest user-mode-handoff-restores-palettes-and-reopens-display
  (let [h (ready! (harness)) receive (last @(:callbacks h)) device (:session h)]
    (receive [0x90 36 127])
    (receive [0xb0 59 127])
    (is (= :suspended (:status (session/snapshot device))))
    (is (= 1 (count (filter #(= [:display/close] %) @(:log h)))))
    (is (every? #(= :releasing (:phase %)) (vals (:instances @(:show h)))))
    (is (some #(= [:midi/send (codec/palette-write 0 36 [36 0 0 31])] %) @(:log h)))
    (let [before (:revision @(:show h))]
      (receive [0x90 37 127])
      (is (= before (:revision @(:show h)))))
    (receive [0xb0 59 127])
    (is (= :active (:status (session/snapshot device))))
    (is (= 2 @(:display-count h)))
    (is (false? (get-in (session/snapshot device) [:local :ready?])))
    (session/close! device)
    (session/close! device)
    (is (= 1 (count (filter #(= [:midi/close] %) @(:log h)))))))

(deftest disconnect-releases-holds-skips-restoration-and-rejects-stale-callbacks
  (let [h (ready! (harness)) old-receive (first @(:callbacks h)) device (:session h)]
    (old-receive [0x90 36 127])
    (let [before (count (filter #(= :midi/send (first %)) @(:log h)))]
      (session/close! device true)
      (is (= before (count (filter #(= :midi/send (first %)) @(:log h))))))
    (is (every? #(= :releasing (:phase %)) (vals (:instances @(:show h)))))
    (session/open! device)
    (let [before (session/snapshot device)]
      (old-receive [0x90 37 127])
      (is (= before (session/snapshot device))))
    (session/close! device)))

(deftest partial-open-failure-closes-acquired-midi
  (let [h (harness {:display {:open! #(throw (ex-info "display failed" {}))}})]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"display failed" (session/open! (:session h))))
    (is (= :failed (:status (session/snapshot (:session h)))))
    (is (= 1 (count (filter #(= [:midi/close] %) @(:log h)))))))

(deftest missing-native-library-also-cleans-up-acquired-midi
  (let [h (harness {:display {:open! #(throw (UnsatisfiedLinkError. "native unavailable"))}})]
    (is (thrown? UnsatisfiedLinkError (session/open! (:session h))))
    (is (= :failed (:status (session/snapshot (:session h)))))
    (is (= 1 (count (filter #(= [:midi/close] %) @(:log h)))))))

(deftest independent-sessions-cannot-close-or-change-each-other
  (let [a (ready! (harness)) b (ready! (harness {:session-id "device-b"}))]
    ((last @(:callbacks a)) [0x90 36 127])
    ((last @(:callbacks b)) [0x90 37 127])
    (let [before-b @(:log b)]
      (session/close! (:session a))
      (is (= before-b @(:log b)))
      (is (= :active (:status (session/snapshot (:session b)))))
      (is (= :running (:phase (first (vals (:instances @(:show b))))))))
    (session/close! (:session b))))

(deftest palette-and-led-timeouts-do-not-invent-capabilities-or-flood
  (let [h (harness {:profile (push/profile {:timeout-ms 100})})]
    (session/open! (:session h))
    (reset! (:now h) 101)
    (session/refresh! (:session h))
    (is (= :palette-timeout (get-in (session/snapshot (:session h)) [:failure :code])))
    (is (= :failed (:status (session/snapshot (:session h)))))
    (is (= 1 (count (filter #(= :midi/send (first %)) @(:log h)))))
    (session/close! (:session h)))
  (let [h (ready! (harness {:profile (push/profile {:timeout-ms 100})}))]
    (doseq [time [101 202 303]] (reset! (:now h) time) (session/refresh! (:session h)))
    (is (= :led-timeout (get-in (session/snapshot (:session h)) [:failure :code])))
    (is (= :failed (:status (session/snapshot (:session h)))))
    (let [before @(:log h)]
      (session/refresh! (:session h))
      (is (= before @(:log h))))
    (session/close! (:session h))))

(deftest generic-midi-osc-and-sensor-use-same-command-path
  (doseq [[profile messages expected]
          [[(generic/profile {:kind :midi :bindings [{:event {:type :control-change :controller 7}
                                                      :command {:op :master/set} :output-range [0 1]}]})
            [[0xb0 7 127]] 1.0]
           [(generic/profile {:kind :osc :mappings {"/master" {:op :master/set}}})
            [{:path "/master" :args [0.3]}] 0.3]
           [(generic/profile {:kind :sensor :bindings [{:event {:control :distance}
                                                        :command {:op :master/set}
                                                        :input-range [0 100] :output-range [0 1]}]})
            [{:control :distance :value 25}] 0.25]]]
    (let [h (harness {:profile profile :display nil})]
      (session/open! (:session h))
      (doseq [message messages] ((last @(:callbacks h)) message))
      (is (== expected (:master @(:show h))))
      (session/close! (:session h)))))

(deftest generic-note-holds-ignore-pressure-and-release-on-close
  (let [profile (generic/profile {:bindings [{:event {:type :note-on :note 60} :cue-id :held}]})
        h (harness {:profile profile :display nil})]
    (session/open! (:session h))
    ((last @(:callbacks h)) [0xa0 60 127])
    (is (= {} (:instances @(:show h))))
    ((last @(:callbacks h)) [0x90 60 127])
    (is (= 1 (count (:instances @(:show h)))))
    (session/close! (:session h))
    (is (= :releasing (:phase (first (vals (:instances @(:show h)))))))))

(deftest scheduling-is-owned-and-old-ticks-cannot-affect-resumed-session
  (let [ticks (atom []) cancellations (atom 0)
        h (harness {:schedule! (fn [tick] (swap! ticks conj tick) #(swap! cancellations inc))})
        device (:session h)]
    (session/open! device)
    (is (= 1 (count @ticks)))
    (session/suspend! device)
    (is (= 1 @cancellations))
    (session/resume! device)
    (is (= 2 (count @ticks)))
    (let [before (session/snapshot device)]
      ((first @ticks))
      (is (= before (session/snapshot device))))
    (session/close! device)
    (is (= 2 @cancellations))))

(deftest transport-failure-closes-owned-resources-and-releases-holds
  (let [h (ready! (harness)) device (:session h) receive (last @(:callbacks h))]
    (receive [0x90 36 127])
    ;; Replacement transport fails only when feedback next writes. The session
    ;; still owns the acquired handles and must release them exactly once.
    (let [failing (assoc-in device [:options :midi :send!]
                           (fn [_ _] (throw (ex-info "unplugged" {}))))]
      (session/receive! failing [0xf0 0 0x21 0x1d 0 1 9 100 0xf7])
      (is (= :failed (:status (session/snapshot failing))))
      (is (every? #(= :releasing (:phase %)) (vals (:instances @(:show h)))))
      (is (= 1 (count (filter #(= [:midi/close] %) @(:log h)))))
      (is (= 1 (count (filter #(= [:display/close] %) @(:log h))))))))

(deftest model-epoch-change-clears-gestures-but-retains-physical-palette-ownership
  (let [h (ready! (harness)) receive (last @(:callbacks h)) device (:session h)]
    (receive [0x90 36 127])
    (reset! (:show h) (model/new-show (assoc (dissoc @(:show h) :control) :epoch 1 :instances {})))
    (session/refresh! device)
    (is (= {} (get-in (session/snapshot device) [:local :holds])))
    (is (= 128 (count (get-in (session/snapshot device) [:local :palettes]))))
    (receive [0x80 36 0])
    (is (= {} (:instances @(:show h))))
    (session/close! device)))

(deftest sensor-thresholds-have-edge-semantics
  (let [profile (generic/profile {:kind :sensor
                                  :bindings [{:id :duck-motion :event {:control :motion}
                                              :cue-id :held :threshold 0.6}]})
        h (harness {:profile profile :display nil})]
    (session/open! (:session h))
    (doseq [value [0.2 0.7 0.8 0.9]] ((last @(:callbacks h)) {:control :motion :value value}))
    (is (= 1 (count (:instances @(:show h)))))
    ((last @(:callbacks h)) {:control :motion :value 0.1})
    (is (= :releasing (:phase (first (vals (:instances @(:show h)))))))
    (session/close! (:session h))))

(deftest idle-device-watchdog-detects-disconnection-and-releases-held-cues
  (let [h (ready! (harness {:profile (push/profile {:timeout-ms 100})}))
        device (:session h) receive (last @(:callbacks h))]
    (dotimes [_ 8] (led-ack! h))
    (receive [0x90 36 127])
    (dotimes [_ 2] (led-ack! h))
    (reset! (:now h) 51)
    (session/refresh! device)
    (is (= [:midi/send (codec/sysex 0 [9])] (last (filter #(= :midi/send (first %)) @(:log h)))))
    (doseq [time [152 253 354]] (reset! (:now h) time) (session/refresh! device))
    (is (= :failed (:status (session/snapshot device))))
    (is (every? #(= :releasing (:phase %)) (vals (:instances @(:show h)))))
    (is (= 1 (count (filter #(= [:midi/close] %) @(:log h)))))))

(deftest simultaneous-devices-share-one-authoritative-dispatcher-without-lost-commands
  (let [profile (generic/profile {:bindings [{:event {:type :control-change :controller 7}
                                             :command {:op :master/set} :output-range [0 1]}]})
        a (harness {:profile profile :display nil})
        b (harness {:session-id "device-b" :profile profile :display nil
                    :model! (get-in a [:options :model!])
                    :dispatch! (get-in a [:options :dispatch!])})
        gate (promise)]
    (session/open! (:session a))
    (session/open! (:session b))
    (let [jobs (mapv (fn [h]
                       (future @gate
                               (dotimes [n 50] ((last @(:callbacks h)) [0xb0 7 n])))) [a b])]
      (try
        (deliver gate true)
        (is (every? #(not= ::timeout (deref % 5000 ::timeout)) jobs))
        (is (= 100 (:revision @(:show a))))
        (let [commands (map second (filter #(= :command (first %)) @(:log a)))]
          (is (= 100 (count (set (map :command-id commands)))))
          (is (= #{"device-a" "device-b"} (set (map #(get-in % [:source :session-id]) commands)))))
        (finally
          (doseq [job jobs] (future-cancel job))
          (session/close! (:session a))
          (session/close! (:session b)))))))

(deftest closing-resources-does-not-depend-on-host-model-availability
  (let [h (harness) device (:session h)]
    (session/open! device)
    (session/close! (assoc-in device [:options :model!]
                             #(throw (ex-info "host stopped" {}))))
    (is (= :closed (:status (session/snapshot device))))
    (is (= 1 (count (filter #(= [:midi/close] %) @(:log h)))))
    (is (= 1 (count (filter #(= [:display/close] %) @(:log h)))))
    (is (some #{"host stopped"} (:errors (session/snapshot device))))))

(deftest visualization-feedback-owns-only-its-mounted-session
  (let [model (initial-model)
        operations (atom []) seen-input (atom nil)
        source {:open! #(do (swap! operations conj :open) :surface)
                :project! (fn [_ _ m] (assoc m :projected true))
                :close! (fn [_] (swap! operations conj :close))}
        profile {:id :test :input (fn [state _ m _] (reset! seen-input m) {:state state})
                 :feedback (fn [state m _] (swap! operations conj (:projected m)) {:state state})}
        device (session/create {:session-id "display" :profile profile :feedback-source source
                                :model! (constantly model) :now-ms! (constantly 0) :dispatch! identity})]
    (session/open! device)
    (session/receive! device :press)
    (is (identical? model @seen-input))
    (session/suspend! device)
    (let [before @operations]
      (session/refresh! device)
      (is (= before @operations)))
    (session/resume! device)
    (session/close! device)
    (is (= [:open true true :close :open true :close] @operations))))

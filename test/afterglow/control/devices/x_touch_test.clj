(ns afterglow.control.devices.x-touch-test
  (:require [clojure.test :refer :all]
            [afterglow.control.model :as control]
            [afterglow.control.devices.session :as session]
            [afterglow.control.devices.x-touch :as touch]))

(defn cue-id [n] (keyword (str "cue-" n)))

(defn initial-model []
  (control/new-show
   {:registry {:effects {:wash {:id :wash :version 1
                                :params {:level {:type :number :default 0.5 :bounds [0 1]}
                                         :enabled {:type :boolean :default false}
                                         :mode {:type :enum :values [:a :b :c] :default :b}
                                         :color {:type :color :default [1 0 0]}}}}
               :cues (into {} (for [n (range 40)] [(cue-id n) {:id (cue-id n) :version 1 :effect-id :wash :name (str "Cue " n)}]))}}))

(defn harness []
  (let [model (atom (initial-model)) commands (atom []) now (atom 0) callbacks (atom {}) log (atom [])]
    {:model model :commands commands :now now :callbacks callbacks :log log
     :channels (mapv #(hash-map :cue-id (cue-id %) :label (str "Cue " %) :color [1 0 0]) (range 40))
     :transport (fn [id]
                  {:open! #(do (swap! callbacks assoc id %) (swap! log conj [:open id]) id)
                   :send! (fn [_ messages] (swap! log into (map #(vector :send id %) messages)))
                   :close! (fn [_] (swap! log conj [:close id]))})
     :options {:model! #(deref model) :now-ms! #(deref now) :schedule! nil
               :dispatch! (fn [command]
                            (locking model
                              (swap! commands conj command)
                              (let [result (control/apply-command @model command)]
                                (reset! model (:model result)) result)))}}))

(defn options [h id overrides]
  (merge (:options h) {:session-id id :channels (:channels h) :transport ((:transport h) id)} overrides))

(defn input! [h id bytes] ((get @(:callbacks h) id) bytes))

(defn instance-for [h cue] (last (sort-by :order (filter #(= cue (:cue-id %)) (vals (:instances @(:model h)))))))

(defn sent [h] (mapv #(nth % 2) (filter #(= :send (first %)) @(:log h))))

(deftest touch-gated-faders-and-relative-encoders-drive-real-validated-parameters
  (let [h (harness) device (touch/connect! (options h "main" {}))]
    (try
      (input! h "main" [144 24 127])
      (is (= :persistent (:launch-mode (instance-for h :cue-0))))
      (input! h "main" [224 127 127])
      (is (= 0.5 (get-in (instance-for h :cue-0) [:params :level])) "untouched motor echo is ignored")
      (input! h "main" [144 104 127])
      (reset! (:log h) [])
      (input! h "main" [224 0 32])
      (is (= (/ 4096.0 16383.0) (get-in (instance-for h :cue-0) [:params :level])))
      (is (not-any? #(= 224 (first %)) (sent h)) "feedback never fights the touched fader")
      (input! h "main" [128 104 127])
      (is (some #(= [224 0 32] %) (sent h)))
      (input! h "main" [176 16 65])
      (is (< (Math/abs (- (- (/ 4096.0 16383.0) 0.01) (get-in (instance-for h :cue-0) [:params :level]))) 1.0e-12))
      (is (every? #(= :x-touch (get-in % [:source :adapter])) @(:commands h)))
      (finally (session/close! device)))))

(deftest held-cues-touch-ownership-and-feedback-diffs-survive-banking
  (let [h (harness) device (touch/connect! (options h "main" {}))]
    (try
      (input! h "main" [144 0 127])
      (let [held (instance-for h :cue-0)]
        (is (= :held (:launch-mode held)))
        (input! h "main" [144 104 127])
        (input! h "main" [144 47 127])
        (is (= 8 (get-in (session/snapshot device) [:local :bank])))
        (input! h "main" [144 24 127])
        (is (instance-for h :cue-8))
        (input! h "main" [224 127 127])
        (is (= 1.0 (get-in (instance-for h :cue-0) [:params :level])) "touch remains attached to its original activation")
        (is (= 0.5 (get-in (instance-for h :cue-8) [:params :level])))
        (input! h "main" [128 0 127])
        (is (= :releasing (:phase (get-in @(:model h) [:instances (:id held)]))))
        (is (= :running (:phase (instance-for h :cue-8)))))
      (input! h "main" [128 104 0])
      (reset! (:log h) [])
      (session/refresh! device)
      (session/refresh! device)
      (is (empty? (sent h)) "unchanged feedback is diffed, not resent")
      (finally (session/close! device)))))

(deftest typed-controls-and-master-have-explicit-schema-mapping
  (let [h (harness) channels (assoc (:channels h) 0 {:cue-id :cue-0 :fader :enabled :encoder :mode})
        device (touch/connect! (options h "main" {:channels channels}))]
    (try
      (input! h "main" [144 24 127])
      (input! h "main" [144 104 127])
      (input! h "main" [224 127 127])
      (is (true? (get-in (instance-for h :cue-0) [:params :enabled])))
      (input! h "main" [176 16 1])
      (is (= :c (get-in (instance-for h :cue-0) [:params :mode])))
      (input! h "main" [144 32 127])
      (is (= :b (get-in (instance-for h :cue-0) [:params :mode])))
      (input! h "main" [144 112 127])
      (input! h "main" [232 0 0])
      (is (= 0.0 (:master @(:model h))))
      (input! h "main" [144 93 127])
      (is (false? (get-in @(:model h) [:transport :playing?])))
      (input! h "main" [144 94 127])
      (is (true? (get-in @(:model h) [:transport :playing?])))
      (finally (session/close! device)))))

(deftest two-independent-sessions-do-not-share-touch-holds-or-port-lifecycle
  (let [h (harness) main (touch/connect! (options h "main" {}))
        xt (touch/connect! (options h "xt" {:extender? true :channel-offset 8}))]
    (try
      (input! h "main" [144 0 127])
      (input! h "xt" [144 0 127])
      (is (= #{:cue-0 :cue-8} (set (map :cue-id (vals (:instances @(:model h)))))))
      (is (some #(and (= [240 0 0 102 21 114] (take 6 %)) (= 247 (last %))) (sent h)))
      (let [old-input (get @(:callbacks h) "main")]
        (session/close! main)
        (is (= :releasing (:phase (instance-for h :cue-0))))
        (is (= :running (:phase (instance-for h :cue-8))))
        (old-input [144 24 127])
        (is (= 2 (count (:instances @(:model h))))))
      (input! h "xt" [144 112 127])
      (input! h "xt" [232 0 0])
      (is (= 1.0 (:master @(:model h))) "XT cannot impersonate a master fader")
      (is (= 1 (count (filter #{[:close "main"]} @(:log h)))))
      (finally (session/close! main) (session/close! xt)))))

(deftest main-and-extender-share-explicit-bank-owner-and-clean-up-partial-start
  (let [h (harness)
        group (touch/connect-group! (merge (:options h)
                                          {:channels (:channels h)
                                           :units [{:session-id "main" :extender? false :transport ((:transport h) "main")}
                                                   {:session-id "xt" :extender? true :transport ((:transport h) "xt")}]}))]
    (try
      (input! h "main" [144 47 127])
      (is (= 16 (:bank (touch/group-status group))))
      (input! h "main" [144 24 127])
      (input! h "xt" [144 24 127])
      (is (= #{:cue-16 :cue-24} (set (map :cue-id (vals (:instances @(:model h)))))))
      (input! h "main" [144 48 127])
      (is (= 15 (:bank (touch/group-status group))))
      (touch/bank-group! group 0)
      (is (= [0 0] (mapv #(get-in (session/snapshot %) [:local :bank]) (:sessions @(:state group)))))
      (input! h "main" [224 0])
      (is (= [:active :active] (mapv :status (:units (touch/group-status group)))))
      (is (seq (get-in (touch/group-status group) [:units 0 :errors])))
      (finally (touch/close-group! group)))
    (is (= 2 (count (filter #(= :close (first %)) @(:log h)))))
    (is (:closed? (touch/close-group! group)))
    (let [before (count (filter #(= :close (first %)) @(:log h)))]
      (is (thrown? Exception
                   (touch/connect-group!
                    (merge (:options h) {:channels (:channels h)
                                         :units [{:session-id "good" :extender? false :transport ((:transport h) "good")}
                                                 {:session-id "broken" :extender? true
                                                  :transport {:open! (fn [_] (throw (Exception. "injected open failure")))
                                                              :send! (fn [& _]) :close! (fn [_])}}]}))))
      (is (= (inc before) (count (filter #(= :close (first %)) @(:log h))))))))

(deftest group-strip-remapping-and-stale-bank-callbacks-never-reassign-ownership
  (let [h (harness)
        rows (mapv (fn [n] {:group-id [:manual n] :label (str "Group" n) :level 0.5}) (range 18))
        _ (swap! (:model h) assoc :group-rows rows)
        group (touch/connect-group!
               (assoc (:options h) :channels [] :require-touch? false
                      :group-channels :group-rows
                      :group-level-command (fn [id value] {:op :test/level :id id :value value})
                      :units [{:session-id "main" :transport ((:transport h) "main")}
                              {:session-id "xt" :extender? true :transport ((:transport h) "xt")}]))]
    (try
      (input! h "main" [144 104 127])
      (swap! (:model h) update :group-rows subvec 1)
      (input! h "main" [224 127 127])
      (is (empty? @(:commands h)) "Removed target cannot become the new occupant of its strip")
      (input! h "main" [128 104 0])
      (swap! (:model h) assoc :group-rows rows)
      (input! h "main" [144 104 127])
      (input! h "main" [224 127 127])
      (is (empty? @(:commands h)) "A touch before display refresh does not target the new strip")
      (input! h "main" [128 104 0])
      (input! h "main" [224 127 127])
      (is (empty? @(:commands h)) "Group profile still gates echoes when cue-only options would allow them")
      (input! h "main" [144 104 127])
      (input! h "main" [224 127 127])
      (is (= {:op :test/level :id [:manual 0] :value 1.0}
             (select-keys (peek @(:commands h)) [:op :id :value])))
      (input! h "main" [128 104 0])
      (input! h "main" [144 47 127])
      (is (= 16 (:bank (touch/group-status group))))
      (let [[main xt] (:sessions @(:state group))
            bank #(get-in (session/snapshot %) [:local :bank])]
        (is (= [16 16] (mapv bank [main xt])))
        (session/suspend! main)
        (input! h "main" [144 46 127])
        (is (= 16 (:bank (touch/group-status group))))
        (let [stale (get @(:callbacks h) "main")]
          (session/reconnect! main)
          (is (= [16 16] (mapv bank [main xt])))
          (stale [144 46 127])
          (is (= 16 (:bank (touch/group-status group)))))
        (input! h "main" [144 46 127])
        (is (= [0 0] (mapv bank [main xt]))))
      (finally (touch/close-group! group)))))

(deftest component-mapping-preserves-other-components-and-invalid-profiles-stay-inert
  (let [h (harness)
        device (touch/connect! (options h "main" {:channels [{:cue-id :cue-0 :fader {:param :color :component 1}}]}))]
    (try
      (input! h "main" [144 24 127])
      (input! h "main" [144 104 127])
      (input! h "main" [224 127 127])
      (is (= [1 1.0 0] (get-in (instance-for h :cue-0) [:params :color])))
      (finally (session/close! device)))
    (reset! (:log h) [])
    (doseq [channels [[{:color [1 0 0]}] [{:cue-id :cue-0 :color [2 0 0]}]
                      [{:cue-id :cue-0 :fader {:param :color :component -1}}]]]
      (is (thrown? clojure.lang.ExceptionInfo (touch/connect! (options h "invalid" {:channels channels})))))
    (is (empty? @(:log h)))))

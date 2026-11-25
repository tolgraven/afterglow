(ns afterglow.control.devices.push-2-test
  (:require [clojure.test :refer [deftest is testing]]
            [afterglow.control.display :as display]
            [afterglow.control.devices.session :as session]
            [afterglow.control.devices.session-test :as fixture]
            [afterglow.control.devices.push-2 :as push]
            [afterglow.control.codecs.push-2 :as codec]
            [afterglow.control.model :as model]
            [afterglow.control.pages :as pages]
            [afterglow.control.views :as views]
            [afterglow.render.frame :as frame]
            [afterglow.render.frame-test :refer [assignment bytes-at]]))

(def sine {:signal-id :sine :version 1})
(def saw {:signal-id :saw :version 2})
(def schemas
  {:enabled {:type :boolean :default false}
   :level {:type :number :default 0.5 :bounds [0 1]}
   :count {:type :integer :default 2 :bounds [0 16]}
   :wave {:type :enum :default sine :values [sine saw] :widget :waveform}
   :color {:type :color :default [0.5 0.25 0.25]}
   :position {:type :vector :size 3 :default [0 0 0] :bounds [-1 1]}
   :span {:type :range :default [0.2 0.8] :bounds [0 1]}
   :last {:type :number :default 0 :bounds [0 1]}
   :ninth {:type :number :default 0 :bounds [0 1]}
   :tenth {:type :number :default 0 :bounds [0 1]}})
(def order [:enabled :level :count :wave :color :position :span :last :ninth :tenth])
(defn harness
  ([] (harness schemas))
  ([parameter-schemas]
   (let [h (fixture/harness)]
    (swap! (:show h) assoc-in [:registry :effects :wash :params] parameter-schemas)
    (swap! (:show h) assoc-in [:registry :effects :wash :param-order] order)
    (fixture/ready! h))))
(defn local [h] (:local (session/snapshot (:session h))))
(defn view [h] (push/display-view (local h) @(:show h)))
(defn receive! [h bytes] ((last @(:callbacks h)) bytes))
(defn launch! [h note]
  (receive! h [0x90 note 127])
  (:selected-instance (local h)))
(defn values [h id] (get-in @(:show h) [:instances id :params]))
(defn finish! [h]
  (is (= [] (:errors (session/snapshot (:session h)))))
  (session/close! (:session h)))

(defn- gesture-harness [authority before-command!]
  (let [{:keys [show log options] :as h} (fixture/harness)
        device (session/create
                 (assoc options :profile (push/profile {:operator-gestures? true})
                                :dispatch! (fn [command]
                                             (when before-command! (before-command! show command))
                                             (swap! log conj [:command command])
                                             (let [result (model/apply-command @show command authority)]
                                               (reset! show (:model result))
                                               result))))]
    (fixture/ready! (assoc h :session device))))

(def ^:private push-operator {:operator-id "push-2-test"})

(defn- admitted-commands [h]
  (mapv second (filter #(= :command (first %)) @(:log h))))

(defn- pending-sample-harness []
  (let [{:keys [show options] :as h} (fixture/harness {:profile (push/profile {:operator-gestures? true})}
                                                     push-operator)
        apply! (:dispatch! options)
        after-model-read (atom nil)
        complete-sample (atom nil)
        device (session/create
                 (assoc options
                        :model! (fn []
                                  (let [snapshot @show]
                                    (when-let [after-read (first (reset-vals! after-model-read nil))]
                                      (after-read))
                                    snapshot))
                        :dispatch! (fn [{:keys [op sequence] :as command}]
                                     (if (and (= :gesture/sample op) (= 1 sequence))
                                       (let [completion (promise)]
                                         (reset! complete-sample #(deliver completion (:ack (apply! command))))
                                         {:status :pending :completion completion})
                                       (apply! command)))))]
    (fixture/ready! (assoc h :session device :after-model-read after-model-read
                            :complete-sample complete-sample :apply! apply!))))

(deftest pending-encoder-sample-reloads-the-edit-basis-before-the-next-detent
  (let [{:keys [after-model-read complete-sample] :as h} (pending-sample-harness)]
    (try
      (let [id (launch! h 37)]
        (receive! h [0x90 0 127])
        (receive! h [0xb0 71 1])
        (is (= 0.5 (:level (values h id))))
        ;; Commit after receive! has selected its first snapshot and before reconciliation.
        (reset! after-model-read @complete-sample)
        (receive! h [0xb0 71 1])
        (is (= [[1 0.51] [2 0.52]] (mapv (juxt :sequence :value)
                                          (filter #(= :gesture/sample (:op %)) (admitted-commands h)))))
        (receive! h [0x80 0 0])
        (is (= 0.52 (:level (values h id))))
        (is (= 0.52 (get-in @(:show h) [:control :edit-history :nodes 1 :after]))))
      (finally (finish! h)))))

(deftest pending-encoder-reconciliation-discards-input-crossing-an-epoch
  (let [{:keys [session show callbacks after-model-read complete-sample apply!] :as h} (pending-sample-harness)]
    (try
      (let [old-receive (last @callbacks)
            owner-command! (fn [command]
                             (apply! (merge (select-keys @show [:show-id :epoch :time-ms])
                                            {:source {:adapter :test}} command)))]
        (launch! h 37)
        (old-receive [0x90 0 127])
        (old-receive [0xb0 71 1])
        (reset! after-model-read #(do (@complete-sample)
                                      (owner-command! {:op :show/restart :command-id "restart"})
                                      (owner-command! {:op :cue/launch :cue-id :latched :command-id "replacement"})))
        (old-receive [0xb0 71 1])
        (is (= :cue/launch (:op (peek (admitted-commands h)))))
        (is (= (:epoch @show) (:epoch (session/snapshot session))))
        (is (empty? (:encoder-gestures (local h))))
        (is (= [0.5] (mapv #(get-in % [:params :level]) (vals (:instances @show)))))
        (session/close! session true)
        (fixture/ready! h)
        (let [before (admitted-commands h)]
          (old-receive [0x80 0 0])
          (old-receive [0xb0 71 1])
          (is (= before (admitted-commands h)))))
      (finally (finish! h)))))

(deftest encoder-commands-cannot-cross-an-epoch-between-input-and-dispatch
  (doseq [[op event] [[:gesture/begin [0x90 0 127]]
                      [:gesture/sample [0xb0 71 1]]
                      [:gesture/end [0x80 0 0]]]]
    (testing (str op)
      (let [{:keys [session show after-model-read complete-sample] :as h} (pending-sample-harness)]
        (try
          (let [id (launch! h 37)
                ;; A trusted host may initialize a new epoch with captured instances.
                replacement (model/new-show (update @show :epoch inc))]
            (when (not= :gesture/begin op)
              (receive! h [0x90 0 127]))
            (when (= :gesture/end op)
              (receive! h [0xb0 71 1])
              (@complete-sample)
              (session/refresh! session))
            (let [before (admitted-commands h)]
              (reset! after-model-read #(reset! show replacement))
              (receive! h event)
              (is (= before (admitted-commands h))))
            (when (= :gesture/sample op)
              (is (nil? @complete-sample)))
            (is (nil? (get-in @show [:control :edit-history])))
            (is (= 0.5 (:level (values h id))))
            (is (= (:epoch @show) (:epoch (session/snapshot session))))
            (is (= 128 (count (:palettes (local h))))))
          (finally (finish! h)))))))

(deftest encoder-release-keeps-ownership-until-the-end-is-acknowledged
  (doseq [outcome [:exception :rejected :deferred-rejection :deferred-acceptance]]
    (testing (name outcome)
      (let [{:keys [show options] :as h} (fixture/harness {:profile (push/profile {:operator-gestures? true})}
                                                         push-operator)
            apply! (:dispatch! options)
            ends (atom [])
            completion (promise)
            device (session/create
                     (assoc options :dispatch!
                            (fn [command]
                              (if (and (= :gesture/end (:op command)) (= 1 (count (swap! ends conj command))))
                                (case outcome
                                  :exception (throw (ex-info "end dispatch interrupted" {}))
                                  :rejected {:status :rejected :code :dispatch-busy}
                                  {:status :pending :completion completion})
                                (apply! command)))))
            h (fixture/ready! (assoc h :session device))
            history #(get-in @show [:control :edit-history])]
        (try
          (let [id (launch! h 37)]
            (receive! h [0x90 0 127])
            (receive! h [0xb0 71 1])
            (receive! h [0x80 0 0])
            (is (nil? (:touched-parameter (view h))))
            (is (= {:mode :off} (:last-touch-strip (local h))))
            (receive! h [0xb0 71 1])
            (is (= 0.51 (:level (values h id))))
            (is (= 1 (count (:open (history)))))
            (when (= :deferred-rejection outcome)
              (deliver completion {:status :rejected :code :dispatch-busy}))
            (session/close! device true)
            (if (= :deferred-acceptance outcome)
              (do
                (is (= 1 (count @ends)))
                (deliver completion (:ack (apply! (first @ends)))))
              (is (= 2 (count @ends))))
            (is (= #{1} (set (map :last-sequence @ends))))
            (is (= 1 (:cursor (history))))
            (is (empty? (:open (history))))
            (is (= (if (= :exception outcome) ["end dispatch interrupted"] [])
                   (:errors (session/snapshot device)))))
          (finally (session/close! device true)))))))

(deftest pending-encoder-end-preserves-the-next-physical-touch
  (doseq [[held? end-status] [[true :accepted] [false :accepted] [true :rejected]]]
    (testing (str "retouch held? " held? ", prior end " end-status)
      (let [{:keys [show options now] :as h} (fixture/harness {:profile (push/profile {:operator-gestures? true})}
                                                             push-operator)
            apply! (:dispatch! options)
            deferred-end (atom nil)
            completion (promise)
            device (session/create
                     (assoc options :dispatch!
                            (fn [command]
                              (if (and (= :gesture/end (:op command)) (compare-and-set! deferred-end nil command))
                                {:status :pending :completion completion}
                                (apply! command)))))
            h (fixture/ready! (assoc h :session device))
            history #(get-in @show [:control :edit-history])]
        (try
          (let [id (launch! h 37)]
            (receive! h [0x90 0 127])
            (receive! h [0xb0 71 1])
            (receive! h [0x80 0 0])
            (receive! h [0x90 0 127])
            (receive! h [0x90 0 127])
            (reset! now 250)
            (when-not held? (receive! h [0x80 0 0]))
            (receive! h [0xb0 71 1])
            (is (= 0.51 (:level (values h id))))
            (deliver completion
                     (if (= :accepted end-status)
                       (:ack (apply! (assoc @deferred-end :time-ms @now)))
                       {:status :rejected :code :dispatch-busy}))
            ;; The first detent after acknowledgement uses the newly admitted gesture.
            (receive! h [0xb0 71 1])
            (when held? (receive! h [0x80 0 0]))
            (let [gestures (->> (admitted-commands h) (filter :gesture-id) (partition-by :gesture-id))]
              (is (= (if held? 2 1) (count gestures)))
              (is (every? #(= [:gesture/begin :gesture/sample :gesture/end] (mapv :op %)) gestures))
              (when held?
                (is (= [:main 0 250] ((juxt :show-id :epoch :time-ms) (first (second gestures))))))
              (is (= (if held? [0.51 0.52] [0.51])
                     (mapv #(get-in (history) [:nodes % :after]) (range 1 (inc (:cursor (history)))))))
              (is (empty? (:open (history)))))
            (doseq [[cursor expected] (if held? [[2 0.51] [1 0.5]] [[1 0.5]])]
              (let [ack (:ack (apply! (merge (select-keys @show [:show-id :epoch :time-ms])
                                             {:command-id (str "undo-" cursor) :source :test :op :history/undo
                                              :expected-cursor cursor :expected-history-position (:position (history))})))]
                (is (= :accepted (:status ack)))
                (is (= expected (:level (values h id)))))))
          (finally (finish! h)))))))

(deftest held-encoder-retouch-recovers-after-repeated-transient-end-failures
  (doseq [failure [:busy :deferred-busy :exception]]
    (testing (name failure)
      (let [{:keys [show options now] :as h} (fixture/harness {:profile (push/profile {:operator-gestures? true})}
                                                             push-operator)
            apply! (:dispatch! options)
            attempts (atom [])
            recovered? (atom false)
            completion (promise)
            device (session/create
                     (assoc options :dispatch!
                            (fn [command]
                              (if (= :gesture/end (:op command))
                                (let [count (count (swap! attempts conj (:time-ms command)))]
                                  (cond
                                    (= 1 count) {:status :pending :completion completion}
                                    @recovered? (apply! command)
                                    (= :busy failure) {:status :rejected :code :dispatch-busy}
                                    (= :deferred-busy failure)
                                    {:status :pending :completion (deliver (promise) {:status :rejected :code :dispatch-busy})}
                                    :else (throw (ex-info "end dispatcher unavailable" {}))))
                                (apply! command)))))
            h (fixture/ready! (assoc h :session device))
            history #(get-in @show [:control :edit-history])]
        (try
          (let [id (launch! h 37)]
            (receive! h [0x90 0 127])
            (receive! h [0xb0 71 1])
            (receive! h [0x80 0 0])
            (receive! h [0x90 0 127])
            (deliver completion {:status :rejected :code :dispatch-busy})
            (dotimes [_ 3] (session/refresh! device))
            (is (= [0 0] @attempts))
            (reset! now 99)
            (session/refresh! device)
            (is (= [0 0] @attempts))
            (reset! now 100)
            (dotimes [_ 3] (session/refresh! device))
            (is (= [0 0 100] @attempts))
            (reset! recovered? true)
            (reset! now 199)
            (session/refresh! device)
            (is (= [0 0 100] @attempts))
            (reset! now 200)
            (session/refresh! device)
            (is (= [0 0 100 200] @attempts))
            (receive! h [0xb0 71 1])
            (receive! h [0x80 0 0])
            (is (= [0 0 100 200 200] @attempts))
            (is (= [0.51 0.52] (mapv #(get-in (history) [:nodes % :after]) [1 2])))
            (is (empty? (:open (history))))
            (doseq [[cursor expected] [[2 0.51] [1 0.5]]]
              (let [ack (:ack (apply! (merge (select-keys @show [:show-id :epoch :time-ms])
                                             {:command-id (str "recover-undo-" cursor) :source :test :op :history/undo
                                              :expected-cursor cursor :expected-history-position (:position (history))})))]
                (is (= :accepted (:status ack)))
                (is (= expected (:level (values h id))))))
            (is (= (if (= :exception failure) ["end dispatcher unavailable" "end dispatcher unavailable"] [])
                   (:errors (session/snapshot device)))))
          (finally (session/close! device true)))))))

(deftest released-encoders-retry-independently-without-a-retouch
  (let [{:keys [show options now] :as h} (fixture/harness {:profile (push/profile {:operator-gestures? true})}
                                                         push-operator)
        apply! (:dispatch! options)
        attempts (atom [])
        blocked (atom #{:push-2/encoder-0 :push-2/encoder-1})
        device (session/create
                 (assoc options :dispatch!
                        (fn [{:keys [op control-id time-ms] :as command}]
                          (when (= :gesture/end op) (swap! attempts conj [control-id time-ms]))
                          (if (and (= :gesture/end op) (contains? @blocked control-id))
                            {:status :rejected :code :dispatch-busy}
                            (apply! command)))))
        history #(get-in @show [:control :edit-history])]
    (swap! show update-in [:registry :effects :wash]
           #(-> % (assoc-in [:params :tone] (:level schemas)) (assoc :param-order [:level :tone])))
    (let [h (fixture/ready! (assoc h :session device))]
      (try
        (let [id (launch! h 37)]
          (doseq [note [0 1]]
            (receive! h [0x90 note 127])
            (receive! h [0xb0 (+ 71 note) 1])
            (receive! h [0x80 note 0])
            (receive! h [0x80 note 0]))
          (is (= [0 0] (mapv second @attempts)))
          (is (= 2 (count (:open (history)))))
          (reset! now 99)
          (session/refresh! device)
          (is (= [0 0] (mapv second @attempts)))
          (swap! blocked disj :push-2/encoder-1)
          (reset! now 100)
          (dotimes [_ 3] (session/refresh! device))
          (is (= [[:push-2/encoder-0 0] [:push-2/encoder-1 0]
                  [:push-2/encoder-0 100] [:push-2/encoder-1 100]] @attempts))
          (is (= [:instance-param id :tone] (get-in (history) [:nodes 1 :target])))
          (is (= #{[:instance-param id :level]} (set (keys (:open (history))))))
          (reset! blocked #{})
          (reset! now 200)
          (session/refresh! device)
          (is (= [:push-2/encoder-0 200] (peek @attempts)))
          (is (= 5 (count @attempts)))
          (is (= [:instance-param id :level] (get-in (history) [:nodes 2 :target])))
          (is (empty? (:open (history))))
          (is (= {:level 0.51 :tone 0.51} (values h id))))
        (finally (finish! h))))))

(deftest encoder-end-retry-cannot-cross-an-epoch
  (let [{:keys [show options now] :as h} (fixture/harness {:profile (push/profile {:operator-gestures? true})}
                                                         push-operator)
        apply! (:dispatch! options)
        attempts (atom 0)
        replacement (atom nil)
        device (session/create
                 (assoc options
                        :model! (fn []
                                  (let [snapshot @show]
                                    (when-let [new-show (first (reset-vals! replacement nil))]
                                      (reset! show new-show))
                                    snapshot))
                        :dispatch! (fn [command]
                                     (if (= :gesture/end (:op command))
                                       (do (swap! attempts inc) {:status :rejected :code :dispatch-busy})
                                       (apply! command)))))
        h (fixture/ready! (assoc h :session device))]
    (try
      (let [id (launch! h 37)
            new-show (model/new-show (update @show :epoch inc))]
        (receive! h [0x90 0 127])
        (receive! h [0xb0 71 1])
        (receive! h [0x80 0 0])
        (reset! now 100)
        (reset! replacement new-show)
        (session/refresh! device)
        (is (= 1 @attempts))
        (is (= :stale-epoch (get-in (session/snapshot device) [:last-ack :reason])))
        (is (= 0.5 (:level (values h id))))
        (is (nil? (get-in @show [:control :edit-history])))
        (session/refresh! device)
        (is (empty? (:encoder-gestures (local h)))))
      (finally (finish! h)))))

(deftest released-retouch-never-starts-and-permanent-rejection-stops-retries
  (doseq [stopped-by [:release :permanent-rejection]]
    (testing (name stopped-by)
      (let [{:keys [show options now] :as h} (fixture/harness {:profile (push/profile {:operator-gestures? true})}
                                                             push-operator)
            apply! (:dispatch! options)
            attempts (atom 0)
            recovered? (atom false)
            device (session/create
                     (assoc options :dispatch!
                            (fn [command]
                              (if (= :gesture/end (:op command))
                                (let [attempt (swap! attempts inc)]
                                  (cond
                                    @recovered? (apply! command)
                                    (and (= 2 attempt) (= :permanent-rejection stopped-by))
                                    {:status :rejected :code :operator-required}
                                    :else {:status :rejected :code :dispatch-busy}))
                                (apply! command)))))
            h (fixture/ready! (assoc h :session device))]
        (try
          (launch! h 37)
          (receive! h [0x90 0 127])
          (receive! h [0xb0 71 1])
          (receive! h [0x80 0 0])
          (receive! h [0x90 0 127])
          (is (= 2 @attempts))
          (when (= :release stopped-by)
            (receive! h [0x80 0 0])
            (is (= 2 @attempts)))
          (let [previous-attempts @attempts]
            (reset! recovered? true)
            (doseq [time [100 200 300]]
              (reset! now time)
              (session/refresh! device))
            (is (= (if (= :release stopped-by) (inc previous-attempts) previous-attempts) @attempts))
            (when (= :release stopped-by)
              (is (= 1 (get-in @show [:control :edit-history :cursor])))
              (is (empty? (get-in @show [:control :edit-history :open]))))
            (session/close! device true)
            (is (= (inc previous-attempts) @attempts)))
          (is (= [:cue/launch :gesture/begin :gesture/sample :gesture/end]
                 (mapv :op (admitted-commands h))))
          (let [history (get-in @show [:control :edit-history])]
            (is (= 1 (:cursor history)))
            (is (empty? (:open history))))
          (finally (finish! h)))))))

(deftest encoder-detents-and-touch-strip-share-one-scalar-gesture
  (let [h (gesture-harness push-operator nil)]
    (try
      (let [id (launch! h 37)]
        (receive! h [0x90 0 127])
        (receive! h [0xb0 71 1])
        (receive! h [0xe0 0 0])
        (receive! h [0xb0 71 1])
        (receive! h [0x80 0 0])
        (let [[begin detent strip final-detent end :as commands] (rest (admitted-commands h))
              history (get-in @(:show h) [:control :edit-history])]
          (is (= [:gesture/begin :gesture/sample :gesture/sample :gesture/sample :gesture/end]
                 (mapv :op commands)))
          (is (= 1 (count (set (map :gesture-id [begin detent strip final-detent end])))))
          (is (= [[1 0.51] [2 0.0] [3 0.01]] (mapv (juxt :sequence :value) [detent strip final-detent])))
          (is (= 3 (:last-sequence end)))
          (is (= 0.01 (:level (values h id))))
          (is (= {:target [:instance-param id :level] :before 0.5 :after 0.01}
                 (select-keys (get-in history [:nodes (:cursor history)]) [:target :before :after])))
          (is (empty? (:open history)))))
      (finally (finish! h)))))

(deftest touch-strip-keeps-ordinary-editing-for-a-different-target
  (let [h (gesture-harness push-operator nil)]
    (try
      (let [original (launch! h 37)]
        (receive! h [0x90 0 127])
        (receive! h [0xb0 71 1])
        (let [selected (launch! h 36)]
          (receive! h [0x90 0 127])
          (receive! h [0xe0 0 0])
          (is (= {:op :param/set :instance-id selected :param :level :value 0.0}
                 (select-keys (peek (admitted-commands h)) [:op :instance-id :param :value])))
          (is (= 0.0 (:level (values h selected))))
          (is (= 0.51 (:level (values h original))))
          (receive! h [0x80 0 0])
          (is (= [:cue/launch :gesture/begin :gesture/sample :cue/launch :param/set :gesture/end]
                 (mapv :op (admitted-commands h))))))
      (finally (finish! h)))))

(deftest scalar-encoder-touch-pins-the-target-through-selection-and-commits-once
  (let [h (gesture-harness push-operator nil)]
    (try
      (let [id (launch! h 37) history #(get-in @(:show h) [:control :edit-history])]
        (receive! h [0x90 0 127])
        (receive! h [0x90 0 127])
        (let [other-id (launch! h 36)]
          (is (not= id other-id))
          (dotimes [_ 12] (receive! h [0xb0 71 1]))
          (is (zero? (:cursor (history))))
          (is (> (:level (values h id)) 0.5))
          (is (= 0.5 (:level (values h other-id))))
          (receive! h [0x90 0 0])
          (receive! h [0x80 0 0])
          (receive! h [0xb0 71 1])
          (is (= 0.5 (:level (values h other-id))))
          (let [commands (filterv :gesture-id (filter #(= "gesture" (namespace (:op %))) (admitted-commands h)))
                node (get-in (history) [:nodes (:cursor (history))])]
            (is (= (into [:gesture/begin] (concat (repeat 12 :gesture/sample) [:gesture/end])) (mapv :op commands)))
            (is (= (range 1 13) (keep :sequence commands)))
            (is (= 12 (:last-sequence (peek commands))))
            (is (= 1 (count (set (map :gesture-id commands)))))
            (is (= 1 (:cursor (history))))
            (is (= {:target [:instance-param id :level], :actor "push-2-test", :before 0.5
                    :after (:level (values h id))}
                   (select-keys node [:target :actor :before :after]))))
          (reset! (:now h) 250)
          (receive! h [0xb0 71 1])
          (is (= 0.51 (:level (values h other-id))))
          (is (= :param/set (:op (peek (admitted-commands h)))))))
      (finally (finish! h)))))

(deftest concurrent-automation-protects-the-canonical-value-and-accepted-sequence
  (let [automation! (fn [show command]
                      (when (and (= :gesture/sample (:op command)) (= 2 (:sequence command)))
                        (let [write (assoc (select-keys command [:show-id :epoch :time-ms :instance-id :param])
                                           :op :param/set :value 0.25 :command-id "automation" :source {:adapter :routing})]
                          (reset! show (:model (model/apply-command @show write))))))
        h (gesture-harness push-operator automation!)]
    (try
      (let [id (launch! h 37)]
        (receive! h [0x90 0 127])
        (receive! h [0xb0 71 1])
        (is (= 0.51 (:level (values h id))))
        (receive! h [0xb0 71 1])
        (is (= :history-conflict (:code (:last-ack (session/snapshot (:session h))))))
        (receive! h [0x80 0 0])
        (is (= 0.25 (:level (values h id))))
        (is (= 1 (:last-sequence (peek (admitted-commands h)))))
        (is (= :history-conflict (:discarded (:last-ack (session/snapshot (:session h))))))
        (is (= 0 (get-in @(:show h) [:control :edit-history :cursor])))
        (is (empty? (get-in @(:show h) [:control :edit-history :open]))))
      (finally (finish! h)))))

(deftest unadmitted-history-and-touchless-input-retain-ordinary-control
  (let [h (gesture-harness nil nil)]
    (try
      (let [id (launch! h 37)]
        (receive! h [0xb0 71 1])
        (receive! h [0x90 0 127])
        (receive! h [0xb0 71 1])
        (receive! h [0x80 0 0])
        (is (= 0.52 (:level (values h id))))
        (is (= [:cue/launch :param/set :gesture/begin :param/set]
               (mapv :op (admitted-commands h))))
        (is (nil? (get-in @(:show h) [:control :edit-history]))))
      (finally (finish! h)))))

(deftest suspend-finishes-only-the-accepted-encoder-edit
  (let [h (gesture-harness push-operator nil) device (:session h)]
    (try
      (let [id (launch! h 36)]
        (receive! h [0x90 0 127])
        (receive! h [0x80 0 0])
        (is (= 0 (get-in @(:show h) [:control :edit-history :cursor])))
        (receive! h [0x90 0 127])
        (receive! h [0xb0 71 1])
        (receive! h [0xb0 59 127])
        (is (= :suspended (:status (session/snapshot device))))
        (is (= [:gesture/end :instance/end] (mapv :op (take-last 2 (admitted-commands h)))))
        (is (= 0.51 (:level (values h id))))
        (is (= 1 (get-in @(:show h) [:control :edit-history :cursor])))
        (is (empty? (get-in @(:show h) [:control :edit-history :open]))))
      (finally (finish! h)))))

(deftest push-feedback-indexes-running-cues-once-for-the-display-and-pads
  (let [h (harness) calls (atom 0) active views/active-instances]
    (try
      (let [id (launch! h 37)
            cue (get-in @(:show h) [:instances id :cue-id])
            page (:page-id (local h))]
        (swap! (:show h) assoc-in [:pages page :cells]
               (into {} (for [x (range 8) y (range 8)] [[x y] cue])))
        (with-redefs [views/active-instances (fn [model] (swap! calls inc) (active model))]
          (session/refresh! (:session h))
          (is (= 1 @calls))))
      (finally (finish! h)))))

(deftest every-type-edits-through-real-midi-session-and-command-reducer
  (let [h (harness)]
    (try
      (let [id (launch! h 37)]
        (is (= (subvec order 0 8) (mapv :id (:parameters (view h)))))
        (receive! h [0xb0 71 1])
        (receive! h [0xb0 72 10])
        (receive! h [0xb0 73 3])
        (receive! h [0xb0 74 1])
        (is (= {:enabled true :level 0.6 :count 5 :wave saw}
               (select-keys (values h id) [:enabled :level :count :wave])))
        (receive! h [0xb0 25 127])
        (receive! h [0xb0 76 10])
        (is (= [0 0.2 0] (:position (values h id))))
        (receive! h [0xb0 77 127])
        (is (= [0.19 0.8] (:span (values h id))))
        (receive! h [0xb0 20 127])
        (is (false? (:enabled (values h id)))))
      (finally (finish! h)))))

(deftest parameter-banks-and-active-effect-navigation-keep-instance-identity
  (let [h (harness)]
    (try
      (let [first-id (launch! h 37) second-id (launch! h 36)]
        (receive! h [0xb0 49 127])
        (receive! h [0xb0 63 127])
        (receive! h [0xb0 49 0])
        (is (= {:index 1 :count 2 :total 10 :offset 8} (:parameter-bank (view h))))
        (is (= [:ninth :tenth] (mapv :id (:parameters (view h)))))
        (receive! h [0xb0 71 10])
        (is (= 0.1 (:ninth (values h second-id))))
        (is (= 0 (:ninth (values h first-id))))
        (receive! h [0xb0 62 127])
        (is (= first-id (:instance-id (view h))))
        (is (= 0 (get-in (view h) [:parameter-bank :index])))
        (receive! h [0xb0 63 127])
        (is (= second-id (:instance-id (view h))))
        (is (= 1 (get-in (view h) [:parameter-bank :index])))
        (is (= 2 (count (:active-effects (view h))))))
      (finally (finish! h)))))

(deftest encoder-touch-strip-component-selection-and-picker-do-not-launch-cues
  (let [h (harness)]
    (try
      (let [id (launch! h 37)]
        (receive! h [0x90 4 127])
        (is (= {:instance-id id :param :color :encoder 4 :component 0} (:touched-parameter (view h))))
        (receive! h [0xb0 24 127])
        (receive! h [0xe0 127 127])
        (is (= [0.5 0.0 0.0] (:color (values h id))))
        (receive! h [0x90 36 127])
        (is (= [0.0 0.0 0.0] (:color (values h id))))
        (is (= 1 (count (:instances @(:show h)))))
        (receive! h [0x80 4 0])
        (is (nil? (:touched-parameter (view h))))
        (receive! h [0x90 3 127])
        (receive! h [0x90 37 127])
        (is (= saw (:wave (values h id))))
        (is (= :running (get-in @(:show h) [:instances id :phase])))
        (receive! h [0x80 3 0])
        (receive! h [0xe0 0 0])
        (is (= saw (:wave (values h id)))))
      (finally (finish! h)))))

(deftest multiple-touches-fine-control-and-stale-instance-are-isolated
  (let [h (harness)]
    (try
      (let [first-id (launch! h 37) second-id (launch! h 36)]
        (receive! h [0x90 1 127])
        (receive! h [0x90 2 127])
        (receive! h [0x80 2 0])
        (is (= :level (get-in (view h) [:touched-parameter :param])))
        (receive! h [0xb0 49 127])
        (receive! h [0xb0 72 10])
        (is (= 0.51 (:level (values h second-id))))
        ;; Simulate an external human ending this exact instance through the model.
        (let [show @(:show h)]
          (reset! (:show h) (:model (model/apply-command show {:command-id "external-remove"
                                                              :show-id (:show-id show) :epoch (:epoch show)
                                                              :time-ms 0 :source {:adapter :web}
                                                              :op :instance/remove :instance-id second-id}))))
        (receive! h [0xe0 127 127])
        (is (= first-id (:instance-id (view h))))
        (is (nil? (:touched-parameter (view h))))
        (is (= 0.5 (:level (values h first-id)))))
      (finally (finish! h)))))

(def pressure-schemas
  (-> schemas
      (update :level assoc :velocity true :velocity-min 0.2 :velocity-max 0.7)
      (update :count assoc :velocity true :velocity-min 16 :velocity-max 0)))

(deftest velocity-and-pressure-target-the-pressed-instance-and-stop-on-release
  (let [h (harness pressure-schemas)]
    (try
      (let [held-id (launch! h 36) latched-id (launch! h 37)]
        (is (< (Math/abs (- 0.7 (:level (values h held-id)))) 1.0e-9))
        (is (= 0 (:count (values h held-id))))
        (receive! h [0xa0 36 0])
        (is (= 0.2 (:level (values h held-id))))
        (is (= 16 (:count (values h held-id))))
        (is (= 0 (:count (values h latched-id))))
        (is (false? (:enabled (values h held-id))))
        (receive! h [0x80 37 0])
        (receive! h [0xa0 37 0])
        (is (= 0 (:count (values h latched-id))))
        (receive! h [0x80 36 0])
        (receive! h [0xa0 36 127])
        (is (= :releasing (get-in @(:show h) [:instances held-id :phase])))
        (is (= 16 (:count (values h held-id)))))
      (finally (finish! h)))))

(deftest shift-can-latch-a-held-cue-without-release-ending-it
  (let [h (harness pressure-schemas)]
    (try
      (receive! h [0xb0 49 127])
      (let [id (launch! h 36)]
        (is (= :persistent (get-in @(:show h) [:instances id :launch-mode])))
        (receive! h [0xb0 49 0])
        (receive! h [0x80 36 0])
        (is (= :running (get-in @(:show h) [:instances id :phase])))
        (is (= {} (:pads (local h))))
        (receive! h [0xb0 49 127])
        (receive! h [0x90 36 127])
        (is (= :releasing (get-in @(:show h) [:instances id :phase]))))
      (finally (finish! h)))))

(deftest pressure-never-follows-an-external-replacement-or-new-definition
  (let [h (harness pressure-schemas)]
    (try
      (let [id (launch! h 37)
            show @(:show h)
            updated (model/apply-command show {:command-id "replace-definition" :show-id (:show-id show)
                                               :epoch (:epoch show) :time-ms 0 :source :test
                                               :op :registry/publish :kind :effects
                                               :definition (-> (get-in show [:registry :effects :wash])
                                                               (assoc :version 2)
                                                               (assoc-in [:params :count :velocity-max] 16))})]
        (reset! (:show h) (:model updated))
        (receive! h [0xa0 37 0])
        (receive! h [0xa0 37 127])
        (is (= 0 (:count (values h id))) "pressure uses the captured definition")
        (let [removed (model/apply-command @(:show h) {:command-id "remove" :show-id (:show-id show)
                                                      :epoch 0 :time-ms 0 :source :test
                                                      :op :instance/remove :instance-id id})
              replacement (model/apply-command (:model removed) {:command-id "replace" :show-id (:show-id show)
                                                                 :epoch 0 :time-ms 0 :source :test
                                                                 :op :cue/launch :cue-id :latched})
              replacement-id (get-in replacement [:ack :instance-id])]
          (reset! (:show h) (:model replacement))
          (receive! h [0xa0 37 127])
          (is (= 2 (:count (values h replacement-id))))))
      (finally (finish! h)))))

(deftest record-saves-selected-parameters-and-shift-record-clears-future-defaults
  (let [h (harness)]
    (try
      (let [id (launch! h 37)]
        (receive! h [0xb0 72 10])
        (is (= {:saved? false :changed? true :record? false :action :save} (:preset (view h))))
        (receive! h [0xb0 86 127])
        (receive! h [0xb0 20 127])
        (is (= 0.6 (get-in @(:show h) [:registry :cues :latched :saved-params :level])))
        (is (false? (:enabled (values h id))) "Record does not also toggle the top button's boolean")
        (is (= {:saved? true :changed? false :record? true :action :save} (:preset (view h))))
        (receive! h [0xb0 86 0])
        (receive! h [0x80 37 0])
        (receive! h [0x90 37 127])
        (receive! h [0x90 37 127])
        (let [relaunched (launch! h 37)]
          (is (not= id relaunched))
          (is (= 0.6 (:level (values h relaunched))))
          (receive! h [0xb0 49 127])
          (receive! h [0xb0 86 127])
          (receive! h [0xb0 20 127])
          (is (= 3 (get-in @(:show h) [:registry :cues :latched :version])))
          (is (nil? (get-in @(:show h) [:registry :cues :latched :saved-params])))
          (is (= 0.6 (:level (values h relaunched))))
          (is (= {:saved? false :changed? true :record? true :action :clear} (:preset (view h))))))
      (finally (finish! h)))))

(deftest touch-strip-feedback-follows-components-and-restores-on-user-handoff
  (let [h (harness)]
    (try
      (launch! h 37)
      (receive! h [0x90 1 127])
      (is (= {:mode :level :value 8192} (:last-touch-strip (local h))))
      (is (some #{[:midi/send (codec/touch-strip-mode 0 :level)]} @(:log h)))
      (receive! h [0xb0 72 10])
      (is (= {:mode :level :value 9830} (:last-touch-strip (local h))))
      (receive! h [0x90 4 127])
      (is (= :point (get-in (local h) [:last-touch-strip :mode])))
      (receive! h [0xb0 24 127])
      (is (= {:mode :level :value 8192} (:last-touch-strip (local h))))
      (receive! h [0x80 4 0])
      (is (= {:mode :level :value 9830} (:last-touch-strip (local h))))
      (receive! h [0x80 1 0])
      (is (= {:mode :off} (:last-touch-strip (local h))))
      (is (some #{[:midi/send (codec/sysex 0 (into [0x19] (repeat 16 0)))]} @(:log h)))
      (receive! h [0xb0 59 127])
      (is (= :suspended (:status (session/snapshot (:session h)))))
      (is (some #{[:midi/send (codec/touch-strip-mode 0 :default)]} @(:log h)))
      (finally (finish! h)))))

(deftest master-and-manual-tempo-touch-work-without-running-effects
  (let [h (harness)]
    (try
      (receive! h [0x90 8 127])
      (receive! h [0xe0 0 0])
      (is (= 0.0 (:master @(:show h))))
      (is (= {:target :master :editable? true} (:touched-control (view h))))
      (receive! h [0xb0 49 127])
      (receive! h [0xb0 79 10])
      (is (= 0.01 (:master @(:show h))))
      (receive! h [0xb0 49 0])
      (receive! h [0x90 9 127])
      (receive! h [0xb0 15 10])
      (is (= 121.0 (get-in @(:show h) [:transport :bpm])))
      (receive! h [0xb0 49 127])
      (receive! h [0xb0 15 2])
      (is (= 123.0 (get-in @(:show h) [:transport :bpm])))
      (receive! h [0xe0 127 127])
      (is (= 200.0 (get-in @(:show h) [:transport :bpm])))
      (receive! h [0x80 9 0])
      (is (= {:target :master :editable? true} (:touched-control (view h))))
      (receive! h [0xe0 127 127])
      (is (= 1.0 (:master @(:show h))))
      (finally (finish! h)))))

(deftest external-clock-locks-tempo-input-with-explicit-display-feedback
  (let [h (harness)]
    (try
      (swap! (:show h) assoc-in [:transport :source] :beat-link-player-1)
      (receive! h [0x90 9 127])
      (receive! h [0xb0 15 20])
      (receive! h [0xe0 0 0])
      (is (= 120 (get-in @(:show h) [:transport :bpm])))
      (is (= {:target :tempo :editable? false} (:touched-control (view h))))
      (is (= {:mode :off} (:last-touch-strip (local h))))
      (is (empty? (filter #(and (= :command (first %)) (= :transport/set (:op (second %)))) @(:log h))))
      (finally (finish! h)))))

(deftest browse-chooses-one-late-bound-launch-without-triggering-the-picker-pad
  (let [searches (atom [])
        selector {:volume-id :orbit}
        search (fn [_ options] (swap! searches conj options) [{:label "Orbit" :kind :volume :selector selector}])
        h (fixture/ready! (fixture/harness {:profile (push/profile {:target-search search})}))
        launches #(for [[kind c] @(:log h) :when (and (= kind :command) (= :cue/launch (:op c)))] c)]
    (try
      (receive! h [0xb0 111 127])
      (is (= ["Cue defaults" "Orbit"] (mapv :label (get-in (view h) [:target-picker :rows]))))
      (receive! h [0x90 37 127])
      (receive! h [0x90 37 127])
      (is (empty? (launches)))
      (is (= "Orbit" (get-in (view h) [:target-picker :armed :label])))
      (receive! h [0x80 37 0])
      (receive! h [0x90 36 100])
      (is (= selector (get-in (first (launches)) [:launch :selector])))
      (receive! h [0x90 37 100])
      (is (nil? (get-in (last (launches)) [:launch :selector])))
      (is (= 2 (count (launches))))
      (is (= 1 (count @searches)))
      (finally (finish! h)))))

(deftest display-buttons-use-local-state-and-retain-live-pad-ownership
  (let [h (harness)
        cc! (fn [cc v] (receive! h [0xb0 cc v]))
        click! (fn [cc] (cc! cc 127) (cc! cc 0))
        ids (mapv #(keyword (format "page-%02d" %)) (range 11))]
    (try
      (swap! (:show h) update :pages merge (into {} (map (fn [id] [id {:id id :cells {}}]) ids)))
      (let [before @(:show h)]
        (cc! 51 127)
        (cc! 51 127)
        (is (= :pages (:display-mode (view h))))
        (cc! 51 0)
        (click! 63)
        (is (= 1 (:page-bank (view h))))
        (click! 21)
        (is (= :page-08 (:page (view h))))
        (cc! 49 127) (click! 51) (cc! 49 0)
        (is (= :cue (:page-colors (view h))))
        (click! 31)
        (is (= :simulator (:display-mode (view h))))
        (click! 112)
        (is (= :panorama (:camera (view h))))
        (cc! 49 127) (click! 31) (cc! 49 0)
        (is (= :rig (:display-mode (view h))))
        (click! 63)
        (is (= 1 (:fixture-offset (view h))))
        (click! 110)
        (cc! 49 127) (click! 110) (click! 62) (cc! 49 0)
        (is (= [:parameters :history 2] ((juxt :display-mode :parameter-view :history-beats) (view h))))
        (click! 113)
        (is (= :audio (:display-mode (view h))))
        (cc! 49 127) (click! 113) (cc! 49 0)
        (is (= :block-trace (:display-mode (view h))))
        (is (= before @(:show h))))
      (finally (finish! h)))))

(deftest recent-page-selection-launches-and-releases-the-captured-cue
  (let [h (harness)
        click! (fn [cc] (receive! h [0xb0 cc 127]) (receive! h [0xb0 cc 0]))
        top-second (codec/pad-note 1 7)]
    (try
      (launch! h 36)
      (receive! h [0x80 36 0])
      (launch! h 37)
      (let [before @(:show h)]
        (click! 51)
        (click! 21)
        (is (= pages/recent-page-id (:page (view h))))
        (is (= [0 0] (:origin (view h))))
        (is (identical? before @(:show h))))
      (let [held (launch! h top-second)
            instance #(get-in @(:show h) [:instances held])]
        (is (= :held (:cue-id (instance))))
        (is (= :latched (pages/cue-id-at @(:show h) pages/recent-page-id [1 7])))
        (receive! h [0x80 top-second 0])
        (is (= :releasing (:phase (instance)))))
      (click! 20)
      (is (= :main (:page (view h))))
      (finally (finish! h)))))

(deftest parameter-only-display-keeps-top-row-and-navigation-on-parameters
  (let [h (fixture/harness {:profile (push/profile {:display {:display-capabilities display/parameter-only-capabilities}})})
        cc! (fn [cc v] (receive! h [0xb0 cc v]))
        click! (fn [cc] (cc! cc 127) (cc! cc 0))]
    (swap! (:show h) #(-> %
                         (assoc-in [:settings :controllers :push-display] {:mode :pages :parameter-view :history})
                         (assoc-in [:pages :archive] {:id :archive :cells {}})
                         (update-in [:registry :effects :wash] assoc :params schemas :param-order order)))
    (try
      (fixture/ready! h)
      (is (= :parameters (:display-mode (view h))))
      (let [first-id (launch! h 37) second-id (launch! h 36)]
        (click! 20)
        (is (true? (:enabled (values h second-id))))
        (doseq [cc [51 31 110 113 112]] (click! cc))
        (cc! 49 127)
        (doseq [cc [51 31 110 113 112 63]] (click! cc))
        (cc! 49 0)
        (is (= [:ninth :tenth] (mapv :id (:parameters (view h)))))
        (is (= 1 (get-in (view h) [:parameter-bank :index])))
        (click! 62)
        (is (= [:parameters :main first-id] ((juxt :display-mode :page :instance-id) (view h))))
        (is (= {:mode :pages :parameter-view :history} (get-in @(:show h) [:settings :controllers :push-display]))))
      (finally (finish! h)))))

(deftest shift-encoder-follows-the-selected-pan-channel
  (let [coarse {:id :spot :universe 1 :address 1 :channels {:pan 1}}
        fine {:id "spot" :universe 1 :address 2 :channels {:pan [1 2]}}]
    (doseq [rig [[coarse fine] [fine coarse]]]
      (let [h (harness (assoc-in schemas [:level :default] 0.0))]
        (try
          (swap! (:show h) assoc :rig {:fixtures rig})
          (swap! (:show h) assoc-in [:registry :effects :wash :outputs] {:pan {:op :param :key :level}})
          (doseq [[target expected] [[:spot [1 0 0]] ["spot" [0 0 1]]]]
            (swap! (:show h) assoc-in [:registry :effects :wash :targets] [target])
            (let [id (launch! h 36)]
              (receive! h [0xb0 49 127])
              (receive! h [0xb0 72 1])
              (receive! h [0xb0 49 0])
              (let [level (:level (values h id))
                    output (frame/resolve-frame rig [(assignment target :pan level)])]
                (is (= expected (bytes-at output 1 1 2 3))))
              (receive! h [0x80 36 0])))
          (finally (finish! h)))))))

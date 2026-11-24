(ns afterglow.control.devices.push-3-test
  (:require [clojure.test :refer [deftest is]]
            [afterglow.control.model :as model]
            [afterglow.control.pages :as pages]
            [afterglow.control.devices.push-3 :as push]
            [afterglow.control.devices.repl :as devices]
            [afterglow.control.devices.transports :as transports]
            [afterglow.control.devices.session :as session]))

(def layout
  {:pads {[0 0] {:channel 3 :note 12} [1 0] {:channel 3 :note 13}}
   :encoder-touches {:level {:channel 2 :note 9}}
   :encoders {:level {:channel 2 :controller 19} :master {:channel 2 :controller 20}}
   :buttons {:blackout {:channel 4 :controller 22} :right {:channel 4 :controller 23}}
   :touch-strip {:channel 5} :mono-pressure {:channel 3}})

(def options {:layout layout :user-mode? true :expression-mode :poly-aftertouch
              :encoder-bindings {:level {:param :level} :master {:target :master}}
              :button-bindings {:blackout :blackout :right :page-right}
              :pressure-param :level :touch-strip-param :count})

(defn initial-model []
  (model/new-show
    {:registry {:effects {:wash {:id :wash :version 1
                                 :params {:level {:type :number :default 0.5 :bounds [0 1]}
                                          :count {:type :integer :default 5 :bounds [0 10]}}}}
                :cues {:held {:id :held :version 1 :effect-id :wash :held true}
                       :latched {:id :latched :version 1 :effect-id :wash}}}
     :pages {:main {:id :main :cells {[0 0] :held [1 0] :latched}}}}))

(defn harness [profile-options]
  (let [show (atom (initial-model)) log (atom []) receive (atom nil)
        device (session/create
                 {:session-id "push3-capture-test" :profile (push/profile (merge options profile-options))
                  :display (:display profile-options)
                  :model! #(deref show) :now-ms! (constantly 0)
                  :dispatch! (fn [command]
                               (let [result (model/apply-command @show command)]
                                 (swap! log conj command) (reset! show (:model result)) result))
                  :midi {:open! #(do (reset! receive %) :capture)
                         :send! (fn [_ _] (throw (ex-info "Push 3 must not emit unverified bytes" {})))
                         :close! (fn [_] (swap! log conj :closed))}})]
    {:show show :log log :receive receive :device device}))

(deftest actual-session-launches-and-edits-without-outbound-protocol
  (let [{:keys [show log receive device]} (harness {})]
    (try
      (is (= [] @log))
      (session/open! device)
      (@receive [0x93 12 127])
      (let [id (get-in (session/snapshot device) [:local :selected-instance])]
        (is (= :push-3 (get-in @show [:instances id :source :adapter])))
        (@receive [0xb2 19 10])
        (is (= 0.6 (get-in @show [:instances id :params :level])))
        (@receive [0xb2 19 127])
        (is (= 0.59 (get-in @show [:instances id :params :level])))
        (@receive [0xa3 12 127])
        (is (= 1.0 (get-in @show [:instances id :params :level])))
        (@receive [0xe5 127 127])
        (is (= 10 (get-in @show [:instances id :params :count])))
        (@receive [0x92 9 127])
        (is (= #{:level} (get-in (session/snapshot device) [:local :touches])))
        (@receive [0x82 9 0])
        (is (= #{} (get-in (session/snapshot device) [:local :touches])))
        (@receive [0x83 12 0])
        (is (= :releasing (get-in @show [:instances id :phase])))
        (is (= [] (:errors (session/snapshot device)))))
      (finally (session/close! device)))
    (is (= :closed (last @log)))))

(deftest button-and-pad-presses-are-edges-not-repeat-triggers
  (let [{:keys [show receive device]} (harness {})]
    (try
      (session/open! device)
      (doseq [_ (range 3)] (@receive [0x93 13 127]))
      (is (= 1 (count (:instances @show))))
      (is (= :running (:phase (first (vals (:instances @show))))))
      (@receive [0x83 13 0]) (@receive [0x93 13 127])
      (is (= :releasing (:phase (first (vals (:instances @show))))))
      (doseq [_ (range 3)] (@receive [0xb4 22 127]))
      (is (true? (:blackout? @show)))
      (@receive [0xb4 22 0]) (@receive [0xb4 22 127])
      (is (false? (:blackout? @show)))
      (@receive [0xb4 23 127]) (@receive [0xb4 23 127])
      (is (= [8 0] (get-in (session/snapshot device) [:local :origin])))
      (finally (session/close! device)))))

(deftest poly-pressure-is-owned-by-each-held-pad
  (let [{:keys [show receive device]} (harness {:launch-mode :held})]
    (try
      (session/open! device)
      (@receive [0x93 12 127])
      (let [a (get-in (session/snapshot device) [:local :selected-instance])]
        (@receive [0x93 13 127])
        (let [b (get-in (session/snapshot device) [:local :selected-instance])]
          (@receive [0xa3 12 0])
          (is (= 0.0 (get-in @show [:instances a :params :level])))
          (is (= 0.5 (get-in @show [:instances b :params :level])))
          (@receive [0x83 12 0])
          (is (= :releasing (get-in @show [:instances a :phase])))
          (is (= :running (get-in @show [:instances b :phase])))
          (session/suspend! device)
          (is (= :releasing (get-in @show [:instances b :phase])))))
      (finally (session/close! device)))))

(deftest delayed-launch-ack-cannot-reassign-a-repressed-pad
  (let [profile (push/profile options) show (initial-model)
        event ((:decode profile) [0x93 12 127])
        press ((:input profile) (:initial-state profile) event show {:command-id "a"})
        release ((:input profile) (:state press) (assoc event :pressed? false) show {:command-id "release"})
        next-press ((:input profile) (:state release) event show {:command-id "b"})
        late ((:ack profile) (:state next-press) (first (:commands press)) {:status :accepted :instance-id "old"})]
    (is (nil? (get-in late [:state :selected-instance])))
    (is (nil? (get-in late [:state :pads [3 12] :instance-id])))
    (is (= [{:command-id "release" :op :instance/end :instance-id "old"}] (:commands late)))
    (is (= "b" (get-in late [:state :pads [3 12] :gesture-id])))))

(deftest restart-and-old-callback-cannot-release-new-instances
  (let [{:keys [show receive device]} (harness {})]
    (try
      (session/open! device)
      (let [old @receive]
        (old [0x93 12 127])
        (reset! show (model/new-show (assoc (dissoc @show :control) :epoch 1 :instances {})))
        (session/refresh! device)
        (is (= {} (get-in (session/snapshot device) [:local :holds])))
        (old [0x83 12 0])
        (is (= {} (:instances @show)))
        (session/reconnect! device)
        (old [0x93 12 127])
        (is (= {} (:instances @show)))
        (@receive [0x93 12 127])
        (is (= 1 (count (:instances @show)))))
      (finally (session/close! device)))))

(deftest unsupported-modes-and-implicit-mappings-are-rejected
  (doseq [override [{:user-mode? false} {:expression-mode :mpe} {:layout {}}
                    {:encoder-bindings {:unknown {:param :level}}}
                    {:encoder-bindings {:level {:param :level :step -1}}}
                    {:button-bindings {:blackout :invented}}]]
    (is (thrown? clojure.lang.ExceptionInfo (push/profile (merge options override)))))
  (is (thrown? clojure.lang.ExceptionInfo (push/connect! (assoc options :display {})))))

(deftest captured-browse-button-routes-a-single-user-or-mpe-pad-launch
  (doseq [[mode note-a note-b] [[:poly-aftertouch [0x93 12] [0x93 13]] [:mpe [0x91 40] [0x92 41]]]]
    (let [selector {:group-id :wash}
          settings (cond-> {:expression-mode mode :button-bindings {:right :target-picker}
                            :target-search (fn [_ _] [{:label "Wash" :kind :group :selector selector}])}
                     (= :mpe mode) (assoc :zone {:manager-channel 0 :member-channels [1 2]}
                                          :mpe-note-cells {40 [0 0] 41 [1 0]}))
          {:keys [show log receive device]} (harness settings)
          launches #(filter (fn [c] (= :cue/launch (:op c))) @log)]
      (try
        (session/open! device)
        (@receive [0xb4 23 127])
        (@receive (conj note-b 127))
        (@receive (conj note-b 127))
        (is (empty? (launches)))
        (is (= "Wash" (get-in (push/control-view (:local (session/snapshot device)) @show) [:target-picker :armed :label])))
        (@receive (conj note-b 0))
        (@receive (conj note-a 127))
        (is (= selector (get-in (first (launches)) [:launch :selector])))
        (is (nil? (:target-picker (push/control-view (:local (session/snapshot device)) @show))))
        (is (empty? (:errors (session/snapshot device))))
        (finally (session/close! device))))))

(deftest captured-buttons-select-pages-without-launching-cues
  (let [config (assoc options :button-bindings {:blackout :display/pages :right [:display/select-page 1]})
        profile (push/profile config)
        show (assoc-in (initial-model) [:pages :wash] {:id :wash :cells {}})
        press (fn [state cc] ((:input profile) state ((:decode profile) [0xb4 cc 127]) show {}))
        overview (press (:initial-state profile) 22)
        selected (press (:state overview) 23)]
    (is (empty? (:commands selected)))
    (is (= :pages (:display-mode (push/control-view (:state overview) show))))
    (is (= :wash (:page (push/control-view (:state selected) show))))))

(deftest recent-page-selection-routes-user-mode-and-mpe-pads
  (doseq [[mode original recent] [[:poly-aftertouch [0x93 12] [0x93 14]]
                                  [:mpe [0x91 40] [0x92 41]]]]
    (let [bindings {:blackout :display/pages :right [:display/select-page 1]}
          config (cond-> {:expression-mode mode :button-bindings bindings}
                   (= :poly-aftertouch mode) (assoc :layout (assoc-in layout [:pads [0 7]] {:channel 3 :note 14}))
                   (= :mpe mode) (assoc :zone {:manager-channel 0 :member-channels [1 2]}
                                        :mpe-note-cells {40 [0 0] 41 [0 7]}))
          {:keys [show log receive device]} (harness config)]
      (try
        (session/open! device)
        (@receive (conj original 127))
        (let [before @show]
          (@receive [0xb4 22 127])
          (@receive [0xb4 23 127])
          (let [view (push/control-view (:local (session/snapshot device)) @show)]
            (is (= pages/recent-page-id (:page view)))
            (is (= :held (get-in view [:cells 56 :cue :id]))))
          (is (identical? before @show)))
        (@receive (conj recent 127))
        (is (= [:held :held] (mapv :cue-id (filter #(= :cue/launch (:op %)) @log))))
        (is (empty? (:errors (session/snapshot device))))
        (finally (session/close! device))))))

(deftest mpe-page-selection-retains-held-voices-and-routes-new-presses
  (let [options {:expression-mode :mpe :zone {:manager-channel 0 :member-channels [1 2]}
                 :mpe-note-cells {40 [0 0]}
                 :button-bindings {:blackout :display/pages :right [:display/select-page 1]}}
        {:keys [show log receive device]} (harness options)
        launched #(filter (fn [command] (= :cue/launch (:op command))) @log)]
    (try
      (swap! show assoc-in [:pages :wash] {:id :wash :cells {[0 0] :latched}})
      (session/open! device)
      (@receive [0x91 40 100])
      (let [first-instance (:id (first (vals (:instances @show))))]
        (@receive [0xb4 22 127])
        (@receive [0xb4 23 127])
        (@receive [0x92 40 100])
        (is (= [:held :latched] (mapv :cue-id (launched))))
        (@receive [0x81 40 0])
        (is (= first-instance (:instance-id (last (filter #(= :instance/end (:op %)) @log)))))
        (is (empty? (:errors (session/snapshot device)))))
      (finally (session/close! device)))))

(deftest captured-shift-encoder-edits-one-patched-code
  (let [views (atom [])
        display {:device :push-3 :input :view :open! (constantly :capture-display)
                 :render! (fn [_ view] (swap! views conj view)) :close! (fn [_])}
        {:keys [show receive device]} (harness {:button-bindings {:right :shift} :display display})]
    (try
      (swap! show assoc :rig {:fixtures [{:id :light :channels {:pan [1 2]}}]})
      (swap! show assoc-in [:registry :effects :wash :outputs] {:pan {:op :param :key :level}})
      (session/open! device)
      (@receive [0x93 12 100])
      (let [instance (first (keys (:instances @show)))
            level #(get-in @show [:instances instance :params :level])]
        (@receive [0xb2 19 1])
        (is (= 0.51 (level)))
        (let [normal (level) before-shift (peek @views)]
          (is (false? (:fine? before-shift)))
          (@receive [0xb4 23 127])
          (is (= (assoc before-shift :fine? true) (peek @views)))
          (@receive [0xb2 19 1])
          (is (= (+ normal (/ 1.0 65535)) (level)))
          (let [fine (level) before-release (peek @views)]
            (is (true? (:fine? before-release)))
            (@receive [0xb4 23 0])
            (is (= (assoc before-release :fine? false) (peek @views)))
            (@receive [0xb2 19 1])
            (is (= (+ fine 0.01) (level))))))
      (is (empty? (:errors (session/snapshot device))))
      (finally (session/close! device)))))

(deftest tethered-display-follows-captured-controls-and-mpe-selection
  (doseq [[profile-options note] [[{} [0x93 12 100]]
                                  [{:expression-mode :mpe :zone {:manager-channel 0 :member-channels [1 2]}
                                    :mpe-note-cells {40 [0 0]}} [0x91 40 100]]]]
    (let [show (atom (initial-model)) receive (atom nil) views (atom []) lifecycle (atom [])
          surface {:device :push-3 :input :view :open! #(do (swap! lifecycle conj :acquire) :usb)
                   :render! (fn [_ view] (swap! views conj view))
                   :close! (fn [_] (swap! lifecycle conj :release))}
          device (push/connect!
                   (merge options profile-options
                          {:button-bindings {:blackout :display/simulator :right :display/camera}
                           :display surface :session-id "tethered-push" :now-ms! (constantly 0)
                           :model! #(deref show)
                           :dispatch! (fn [command]
                                        (let [ack (model/apply-command @show command)]
                                          (reset! show (:model ack)) ack))
                           :transport {:open! #(do (reset! receive %) :midi)
                                       :send! (fn [_ _] (throw (ex-info "Unexpected MIDI output" {})))
                                       :close! (fn [_])}}))]
      (try
        (is (= :ready (:status (last @views))))
        (session/refresh! device)
        (is (= 1 (count @views)))
        (@receive note)
        (is (= :held (get-in (last @views) [:cue :id])))
        (is (= (:params (get-in @show [:instances (:instance-id (last @views))]))
               (into {} (map (juxt :id :value)) (:parameters (last @views)))))
        (@receive [0xb4 22 127])
        (is (= :simulator (:display-mode (last @views))))
        (@receive [0xb4 23 127])
        (is (= :panorama (:camera (last @views))))
        (session/suspend! device)
        (session/resume! device)
        (is (= [:acquire :release :acquire] @lifecycle))
        (is (empty? (:errors (session/snapshot device))))
        (finally (session/close! device)))
      (is (= [:acquire :release :acquire :release] @lifecycle)))))

(deftest displayed-fallback-instance-receives-encoder-edits
  (doseq [config [{} {:expression-mode :mpe :zone {:manager-channel 0 :member-channels [1 2]}
                      :mpe-note-cells {40 [0 0]}}]]
    (let [opts (assoc-in options [:layout :encoders :level :channel] 6)
          profile (push/profile (merge opts config {:display true}))
          m (initial-model)
          effect (get-in m [:registry :effects :wash])
          instance {:id :current :cue-id :held :effect-id :wash :order 1 :phase :running
                    :params {:level 0.5 :count 5} :definition effect}
          m (assoc-in m [:instances :current] instance)
          old-state (:initial-state profile)
          stale (if (:mpe old-state) (assoc-in old-state [:mpe :selected-instance] :ended)
                    (assoc old-state :selected-instance :ended))
          feedback ((:feedback profile) stale m {})
          raw [0xb6 19 1]
          edit ((:input profile) (:state feedback) ((:decode profile) raw) m {})]
      (is (= :current (get-in feedback [:display :instance-id])))
      (is (= :current (get-in edit [:commands 0 :instance-id])))
      (is (> (get-in edit [:commands 0 :value]) 0.5)))))

(deftest explicit-midi-reaches-the-repl-facade-through-both-input-options
  (doseq [port [:midi :transport]]
    (let [opened (atom [])
          capture {:open! (fn [_] (swap! opened conj :open) :midi)
                   :close! (fn [_] (swap! opened conj :close))}
          config (assoc options port capture :model! initial-model :now-ms! (constantly 0)
                        :session-id "manual-midi" :dispatch! (constantly {:status :accepted}))]
      (with-redefs [transports/midi-transport (fn [_] (throw (ex-info "Unexpected port enumeration" {})))]
        (devices/close! (devices/open-push-3! config)))
      (is (= [:open :close] @opened)))))

(ns afterglow.control.devices.push-3-test
  (:require [clojure.test :refer [deftest is testing]]
            [afterglow.control.model :as model]
            [afterglow.control.pages :as pages]
            [afterglow.control.display :as presentation]
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
                  :model! #(deref show) :now-ms! (or (:now-ms! profile-options) (constantly 0))
                  :dispatch! (fn [command]
                               (let [result (model/apply-command @show command (:authority profile-options))]
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

(defn- overlay-options [display]
  {:layout (-> layout
               (assoc-in [:pads [0 1]] {:channel 3 :note 14})
               (assoc-in [:buttons :variation] {:channel 4 :controller 28}))
   :button-bindings {:variation :variation/cycle :right :page-right}
   :display display
   :pad-overlay {:project (fn [selection _ _]
                            {:view selection
                             :display {:layout (:layout selection)
                                       :cells [{:position [1 0]} {:position [7 7]}]}})
                 :input (fn [selection {:keys [action position]} _ {:keys [presented selected-instance]}]
                          (cond
                            (= :variation/cycle action)
                            {:state (case (:layout selection)
                                      :full (assoc selection :layout :rows)
                                      :rows nil
                                      (when selected-instance {:layout :full :instance-id selected-instance}))}
                            (and presented (= [1 0] position))
                            {:state selection
                             :commands [{:op :param/set :instance-id (:instance-id presented)
                                         :param :count :value 8}]}))}})

(deftest variation-overlay-honors-pad-ownership-and-display-receipts
  (doseq [[mode gesture?] [[:poly-aftertouch false] [:mono-aftertouch true]]]
    (let [frames (atom []) clock (atom 0)
          display {:presentation-receipts? true :open! (constantly :capture) :close! (fn [_])
                   :render! (fn [_ view] (swap! frames conj view))}
          {:keys [show log receive device]}
          (harness (merge (overlay-options display)
                          {:expression-mode mode :cue-gestures? gesture? :hold-ms 100
                           :now-ms! #(deref clock)}))
          cycle! (fn [] (@receive [0xb4 28 127]) (@receive [0xb4 28 0]))
          press! #(@receive [0x93 % 100])
          lift! #(@receive [0x93 % 0])
          pressure! #(if gesture? (@receive [0xd3 %]) (@receive [0xa3 12 %]))
          value #(get-in @show [:instances "0:1" :params %])]
      (testing (name mode)
        (try
          (session/open! device)
          (press! 12)
          (reset! clock 100)
          (session/refresh! device)
          (is (= :running (get-in @show [:instances "0:1" :phase])))
          (cycle!)
          (let [full (peek @frames)]
            (is (= {:layout :full :cells [{:position [1 0]}]} (:pad-overlay full)))
            (press! 13)
            (pressure! 127)
            (is (= 5 (value :count)))
            (is (= (if gesture? 0.5 1.0) (value :level)))
            (lift! 13)
            (pressure! 0)
            (is (zero? (value :level)))
            (cycle!)
            (presentation/presented! full)
            (press! 13)
            (lift! 13)
            (is (= 5 (value :count)))
            (let [rows (peek @frames)]
              (is (= :rows (get-in rows [:pad-overlay :layout])))
              (presentation/presented! (assoc rows :display-mode :pages))
              (press! 13)
              (lift! 13)
              (is (= 5 (value :count)))
              (presentation/presented! rows)
              (press! 13)
              (is (= 8 (value :count)))
              (cycle!)
              (let [live-view (peek @frames)
                    commands (count @log)]
                (is (nil? (:pad-overlay live-view)))
                (press! 13)
                (press! 14)
                (lift! 12)
                (is (= :instance/end (:op (last @log))))
                (is (= (inc commands) (count @log)))
                (is (= :releasing (get-in @show [:instances "0:1" :phase])))
                (presentation/presented! live-view)
                (press! 14)
                (lift! 14)
                (lift! 13)
                (is (= (inc commands) (count @log)))
                (press! 13)
                (lift! 13)
                (is (= [:held :latched] (mapv :cue-id (filter #(= :cue/launch (:op %)) @log)))))))
          (is (empty? (:errors (session/snapshot device))))
          (finally (session/close! device)))))))

(deftest variation-overlay-requires-receipts-and-dedicated-captures
  (let [config (merge options (overlay-options {:presentation-receipts? true}))]
    (doseq [invalid [(dissoc config :display)
                     (assoc config :expression-mode :mpe)
                     (assoc config :button-bindings {})
                     (assoc-in config [:layout :buttons :variation] {:channel 0 :controller 57})
                     (assoc-in config [:layout :buttons :variation] {:channel 0 :controller 49})]]
      (is (thrown? clojure.lang.ExceptionInfo (push/profile invalid))))))

(deftest encoder-overlay-keeps-the-opening-touch-and-captured-pad-owners
  (let [surface (atom nil)
        display {:presentation-receipts? true :open! (constantly :capture) :close! (fn [_])
                 :render! (fn [_ view] (reset! surface view))}
        config (-> (overlay-options display)
                   (assoc-in [:layout :encoder-touches :master] {:channel 2 :note 10})
                   (assoc-in [:pad-overlay :open-encoder]
                             (fn [_ id param positions]
                               (when (and (= :level param) (some #{[1 0]} positions))
                                 {:layout :from-touch :instance-id id}))))
        {:keys [show log receive device]} (harness config)
        press! #(@receive [0x93 % 100])
        lift! #(@receive [0x83 % 0])
        frame! #(presentation/presented! @surface)
        overlay #(get-in @surface [:pad-overlay :layout])]
    (try
      (session/open! device)
      (press! 12)
      (@receive [0x92 9 127])
      (is (= :from-touch (overlay)))
      (let [chooser @surface]
        (press! 13)
        (frame!)
        (press! 13)
        (is (= 5 (get-in @show [:instances "0:1" :params :count])))
        (lift! 13)
        (@receive [0x92 10 127])
        (@receive [0xb2 20 127])
        (@receive [0x82 10 0])
        (is (< (:master @show) 1))
        (@receive [0xb4 28 127])
        (@receive [0xb4 28 0])
        (is (= :from-touch (overlay)))
        (frame!)
        (press! 13)
        (is (= 8 (get-in @show [:instances "0:1" :params :count])))
        (@receive [0x82 9 0])
        (is (nil? (overlay)))
        (presentation/presented! chooser)
        (press! 14)
        (lift! 12)
        (is (= :instance/end (:op (last @log))))
        (frame!)
        (lift! 13)
        (lift! 14)
        (press! 13)
        (is (= [:held :latched] (mapv :cue-id (filter #(= :cue/launch (:op %)) @log)))))
      (is (empty? (:errors (session/snapshot device))))
      (finally (session/close! device)))))

(deftest old-display-receipts-cannot-arm-choices-after-epoch-reset
  (let [surface (atom nil)
        display {:presentation-receipts? true :open! (constantly :capture) :close! (fn [_])
                 :render! (fn [_ view] (reset! surface view))}
        {:keys [show log receive device]} (harness (overlay-options display))]
    (try
      (session/open! device)
      (@receive [0x93 12 100])
      (@receive [0xb4 28 127])
      (@receive [0xb4 28 0])
      (@receive [0x93 13 100])
      (let [old @surface]
        (reset! show (model/new-show (assoc (initial-model) :epoch 1)))
        (session/refresh! device)
        (is (nil? (:pad-overlay @surface)))
        (presentation/presented! old)
        (@receive [0x93 13 100])
        (is (empty? (:instances @show)))
        (presentation/presented! @surface)
        (@receive [0x93 13 100])
        (is (empty? (:instances @show)))
        (@receive [0x93 13 0])
        (@receive [0x93 13 100])
        (is (= [[:held 0] [:latched 1]]
               (mapv (juxt :cue-id :epoch) (filter #(= :cue/launch (:op %)) @log)))))
      (finally (session/close! device)))))

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

(deftest momentary-encoders-own-independent-samples-and-restore-on-their-own-lifts
  (let [now (atom 0)
        settings {:layout (-> layout
                             (assoc-in [:encoders :count] {:channel 2 :controller 21})
                             (assoc-in [:encoder-touches :count] {:channel 2 :note 10}))
                  :encoder-bindings (assoc (:encoder-bindings options) :count {:param :count})
                  :operator-gestures? true
                  :authority {:operator-id :push-3-test} :now-ms! #(deref now)}
        {:keys [show log receive device]} (harness settings)]
    (try
      (swap! show assoc :rig {:fixtures [{:id :light :channels {:pan [1 2]}}]})
      (swap! show assoc-in [:registry :effects :wash :outputs] {:pan {:op :param :key :level}})
      (session/open! device)
      (@receive [0x93 12 100])
      (let [id (first (keys (:instances @show)))
            params #(get-in @show [:instances id :params])
            history #(get-in @show [:control :edit-history])]
        (@receive [0xb0 49 127])
        (@receive [0xb0 57 127])
        (@receive [0x92 9 127])
        (@receive [0x92 10 127])
        (@receive [0x92 9 127])
        (@receive [0xb2 19 1])
        (@receive [0xb2 21 1])
        (is (= (+ 0.5 (/ 1.0 65535)) (:level (params))))
        (is (= 6 (:count (params))))
        (is (= 2 (count (:open (history)))))
        (@receive [0xb0 57 0])
        (@receive [0xb0 49 0])
        (@receive [0xb2 19 1])
        (is (= (+ 0.5 (/ 1.0 65535) 0.01) (:level (params))))
        (@receive [0x92 9 0])
        (@receive [0xb2 19 1])
        (is (= {:level 0.5 :count 6} (params)))
        (@receive [0x82 10 0])
        (is (= {:level 0.5 :count 5} (params)))
        (is (= [:level :count] (mapv :control-id (filter #(= :gesture/cancel (:op %)) @log))))
        (is (every? #(= {:adapter :push-3 :session-id "push3-capture-test"} (:source %)) @log))
        (is (empty? (:open (history))))
        (is (= [0 0] ((juxt :cursor :position) (history))))
        (reset! now 210)
        (@receive [0xb0 49 127])
        (@receive [0x92 9 127])
        (@receive [0xb2 19 1])
        (@receive [0x82 9 0])
        (@receive [0xb0 49 0])
        (is (= (+ 0.5 (/ 1.0 65535)) (:level (params))))
        (is (= [1 1] ((juxt :cursor :position) (history))))
        (is (empty? (:errors (session/snapshot device)))))
      (finally (session/close! device)))))

(deftest accent-default-keeps-captured-addresses-and-migrates-shift-configuration
  (doseq [[settings press] [[{:temporary-encoder-modifier :shift} [0xb0 57]]
                            [{:temporary-encoder-modifier :right} [0xb0 57]]
                            [{:layout (assoc-in layout [:buttons :shift-capture] {:channel 0 :controller 49})
                              :temporary-encoder-modifier :shift-capture} [0xb0 57]]
                            [{:layout (assoc-in layout [:buttons :accent] {:channel 6 :controller 42})} [0xb6 42]]
                            [{:layout (assoc-in layout [:buttons :emphasis] {:channel 0 :controller 57})} [0xb0 57]]]]
    (let [{:keys [show log receive device]}
          (harness (merge {:operator-gestures? true :authority {:operator-id :push-3-test}
                           :button-bindings {:right :shift}} settings))]
      (try
        (session/open! device)
        (@receive [0x93 12 100])
        (let [level #(get-in @show [:instances "0:1" :params :level])]
          (@receive (conj press 127))
          (@receive [0x92 9 127])
          (@receive [0xb2 19 1])
          (is (= 0.51 (level)))
          (@receive (conj press 0))
          (@receive [0x82 9 0])
          (is (= 0.5 (level)))
          (is (= [:cue/launch :gesture/begin :gesture/sample :gesture/cancel] (mapv :op @log))))
        (finally (session/close! device))))))

(deftest factory-accent-keeps-occupied-ccs-and-mpe-member-routing
  (let [base (assoc options :operator-gestures? true)
        address {:channel 0 :controller 57}
        occupied-button (-> base (assoc-in [:layout :buttons :occupied] address)
                            (assoc-in [:button-bindings :occupied] :blackout))
        occupied-encoder (assoc-in base [:layout :encoders :master] address)
        occupied-shift (assoc-in base [:layout :encoders :master] {:channel 0 :controller 49})
        member-zone (assoc base :expression-mode :mpe :mpe-note-cells {40 [0 0]}
                                 :zone {:manager-channel 15 :member-channels (vec (range 15))})]
    (doseq [settings [occupied-button occupied-encoder member-zone]]
      (is (not (contains? (get-in (push/profile settings) [:capabilities :controls]) :temporary-encoder-edits))))
    (is (= :occupied (:control-id ((:decode (push/profile occupied-button)) [0xb0 57 127]))))
    (is (= :master (:control-id ((:decode (push/profile occupied-encoder)) [0xb0 57 127]))))
    (is (= :master (:control-id ((:decode (push/profile occupied-shift)) [0xb0 49 127]))))
    (is (contains? (get-in (push/profile (assoc occupied-button :temporary-encoder-modifier :right))
                           [:capabilities :controls]) :temporary-encoder-edits))
    (is (nil? ((:decode (push/profile options)) [0xb0 57 127])))))

(deftest momentary-encoder-fails-closed-without-an-admitted-touch
  (doseq [[label overrides expected-rejection]
          [["missing touch capture" {:layout (dissoc layout :encoder-touches) :launch? true} nil]
           ["missing selected instance" {} nil]
           ["untrusted host" {:launch? true :authority nil} :operator-required]
           ["unsupported schema" {:launch? true :encoder-bindings {:level {:param :flag}}} nil]]]
    (testing label
      (let [{:keys [show log receive device]}
            (harness (merge {:operator-gestures? true
                             :authority {:operator-id :push-3-test}} overrides))]
        (try
          (swap! show assoc-in [:registry :effects :wash :params :flag] {:type :boolean :default false})
          (session/open! device)
          (when (:launch? overrides) (@receive [0x93 12 100]))
          (@receive [0xb0 57 127])
          (is (= [0 0] (get-in (session/snapshot device) [:local :origin])))
          (@receive [0x92 9 127])
          (when expected-rejection
            (is (= expected-rejection (get-in (session/snapshot device) [:last-ack :code]))))
          (@receive [0xb2 19 12])
          (when (= label "missing selected instance")
            (@receive [0x93 12 100])
            (@receive [0x92 9 127])
            (@receive [0xb0 57 0])
            (@receive [0xb2 19 12]))
          (@receive [0x82 9 0])
          (is (not-any? #(#{:param/set :gesture/sample} (:op %)) @log))
          (is (empty? (get-in @show [:control :edit-history :open])))
          (is (empty? (:errors (session/snapshot device))))
          (finally (session/close! device))))))
  (is (thrown? clojure.lang.ExceptionInfo
               (push/profile (assoc options :temporary-encoder-modifier :right))))
  (is (thrown? clojure.lang.ExceptionInfo
               (push/profile (assoc options :temporary-encoder-modifier :unknown :operator-gestures? true)))))

(deftest epoch-adoption-blocks-a-still-held-temporary-encoder-until-lift
  (let [now (atom 0)
        {:keys [show log receive device]}
        (harness {:temporary-encoder-modifier :right :operator-gestures? true
                  :authority {:operator-id :push-3-test} :now-ms! #(deref now)})]
    (try
      (session/open! device)
      (@receive [0x93 12 100])
      (@receive [0xb4 23 127])
      (@receive [0x92 9 127])
      (@receive [0xb2 19 1])
      (@receive [0xb4 23 0])
      (is (= 0.51 (get-in @show [:instances "0:1" :params :level])))
      (reset! show (assoc (initial-model) :epoch 1))
      (@receive [0x93 12 100])
      (@receive [0x92 9 127])
      (@receive [0xb2 19 14])
      (@receive [0x82 9 0])
      (@receive [0xb2 19 14])
      (is (= 0.5 (get-in @show [:instances "1:1" :params :level])))
      (is (= [:cue/launch] (mapv :op (filter #(= 1 (:epoch %)) @log))))
      (reset! now 210)
      (@receive [0xb2 19 1])
      (is (= 0.51 (get-in @show [:instances "1:1" :params :level])))
      (is (empty? (:errors (session/snapshot device))))
      (finally (session/close! device)))))

(deftest temporary-lift-remains-physical-when-reconciliation-adopts-a-new-show
  (doseq [replace-on [:touch :lift :after-lift]]
    (let [now (atom 1000)
          replace? (atom false)
          {:keys [show log receive device]}
          (harness {:temporary-encoder-modifier :right :operator-gestures? true
                    :authority {:operator-id :push-3-test} :now-ms! #(deref now)})
          replacement (assoc (initial-model) :epoch 1)
          device (update-in device [:options :profile :reconcile]
                           (fn [reconcile]
                             (fn [state model]
                               (if (compare-and-set! replace? true false)
                                 (do (reset! show replacement)
                                     {:state state :refresh-model? true})
                                 (reconcile state model)))))]
      (try
        (session/open! device)
        (@receive [0x93 12 100])
        (@receive [0xb4 23 127])
        (when (= :touch replace-on)
          (reset! now 10)
          (reset! replace? true))
        (@receive [0x92 9 127])
        (if (= :touch replace-on)
          (@receive [0x93 12 100])
          (@receive [0xb2 19 1]))
        (@receive [0xb4 23 0])
        (when (= :lift replace-on)
          (reset! now 10)
          (reset! replace? true))
        (when (= :touch replace-on)
          (@receive [0xb2 19 12])
          (is (= 0.5 (get-in @show [:instances "1:1" :params :level]))))
        (@receive [0x82 9 0])
        (when (= :after-lift replace-on)
          (reset! now 10)
          (reset! show replacement))
        (when-not (= :touch replace-on)
          (@receive [0x93 12 100]))
        (@receive [0xb2 19 1])
        (is (nil? (get-in (session/snapshot device) [:local :encoder-touch-modes :level])))
        (is (= 0.5 (get-in @show [:instances "1:1" :params :level])))
        (is (= [:cue/launch] (mapv :op (filter #(= 1 (:epoch %)) @log))))
        (reset! now 211)
        (@receive [0xb2 19 1])
        (is (= 0.51 (get-in @show [:instances "1:1" :params :level])))
        (is (empty? (:errors (session/snapshot device))))
        (finally (session/close! device))))))

(deftest mpe-fixed-encoder-controls-restore-with-and-without-cue-gestures
  (doseq [cue-gestures? [false true] [modifier press] [[nil [0xb0 57 127]] [:right [0xb4 23 127]]]]
    (let [{:keys [show log receive device]}
          (harness {:expression-mode :mpe :zone {:manager-channel 0 :member-channels [1]}
                    :cue-gestures? cue-gestures? :mpe-note-cells {40 [0 0]}
                    :temporary-encoder-modifier modifier :operator-gestures? true
                    :authority {:operator-id :push-3-test}})]
      (try
        (session/open! device)
        (@receive [0x91 40 100])
        (let [id (first (keys (:instances @show)))
              level #(get-in @show [:instances id :params :level])
              baseline (level)]
          (is (number? baseline))
          (@receive press)
          (@receive [0x92 9 127])
          (@receive [0xb2 19 1])
          (is (= (+ baseline 0.01) (level)))
          (session/suspend! device)
          (is (= baseline (level)))
          (is (= 1 (count (filter #(= :gesture/cancel (:op %)) @log))))
          (is (empty? (:errors (session/snapshot device)))))
        (finally (session/close! device))))))

(deftest mpe-temporary-encoder-pairs-require-fixed-control-addresses
  (let [settings (assoc options :expression-mode :mpe :mpe-note-cells {40 [0 0]}
                                :zone {:manager-channel 0 :member-channels [1]}
                                :operator-gestures? true :temporary-encoder-modifier :right)]
    (is (= :push-3 (:id (push/profile settings))))
    (doseq [section [:encoder-touches :encoders]]
      (let [member-capture (assoc-in settings [:layout section :level :channel] 1)]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"fixed User Mode channels"
                              (push/profile member-capture)))
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"fixed User Mode channels"
                              (push/profile (dissoc member-capture :temporary-encoder-modifier))))
        (doseq [candidate [member-capture (dissoc member-capture :temporary-encoder-modifier)]]
          (is (= :push-3 (:id (push/profile (update-in candidate [:layout :encoder-touches] dissoc :level))))))))))

(defn- launch-test-wash [show]
  (:model (model/apply-command show
            (merge (select-keys show [:show-id :epoch])
                   {:command-id "existing-wash" :time-ms 0 :source :fixture
                    :op :cue/launch :cue-id :held :launch {:mode :persistent}}))))

(deftest shared-parameter-editor-keeps-exact-values-through-momentary-turns
  (doseq [[mode pad] [[:poly-aftertouch [0x93 12 100]] [:mpe [0x91 40 100]]]]
    (testing (name mode)
      (let [calls (atom [])
            editor (fn [_ instance param delta {:keys [mode component fine?]}]
                     (swap! calls conj [param (get-in instance [:params param]) delta mode component fine?])
                     {:value (if fine? 7/11 2/3)})
            settings (cond-> {:expression-mode mode :parameter-editor editor
                              :operator-gestures? true :authority {:operator-id :push-3-test}}
                       (= :mpe mode) (assoc :zone {:manager-channel 0 :member-channels [1]}
                                            :mpe-note-cells {40 [0 0]}
                                            :mapping-policy {:enabled? false}))
            {:keys [show receive device]} (harness settings)
            level #(get-in @show [:instances "0:1" :params :level])]
        (try
          (swap! show assoc-in [:registry :effects :wash :params :level :default] 5/11)
          (session/open! device)
          (@receive pad)
          (is (= 5/11 (level)))
          (@receive [0xb2 19 1])
          (is (= 2/3 (level)))
          (@receive [0xb0 49 127])
          (@receive [0xb0 57 127])
          (@receive [0x92 9 127])
          (@receive [0xb2 19 1])
          (is (= 7/11 (level)))
          (@receive [0xb0 57 0])
          (@receive [0x82 9 0])
          (@receive [0xb0 49 0])
          (is (= 2/3 (level)))
          (is (= [[:level 5/11 1 :relative 0 false] [:level 2/3 1 :relative 0 true]] @calls))
          (is (empty? (get-in @show [:control :edit-history :open])))
          (is (empty? (:errors (session/snapshot device))))
          (finally (session/close! device)))))))

(deftest dedicated-temporary-button-does-not-select-an-active-cue
  (doseq [[mode pad] [[:poly-aftertouch [0x93 12]] [:mpe [0x91 40]]]]
    (testing (name mode)
      (let [settings (cond-> {:expression-mode mode :cue-gestures? true
                              :temporary-encoder-modifier :right :operator-gestures? true
                              :button-bindings {:right :cue-gesture}}
                       (= :mpe mode) (assoc :zone {:manager-channel 0 :member-channels [1]}
                                            :mpe-note-cells {40 [0 0]}))
            {:keys [show log receive device]} (harness settings)]
        (try
          (swap! show launch-test-wash)
          (session/open! device)
          (@receive [0xb4 23 127])
          (@receive (conj pad 100))
          (@receive (conj pad 0))
          (is (= :instance/end (:op (first @log))))
          (is (= :releasing (get-in @show [:instances "0:1" :phase])))
          (is (empty? (:errors (session/snapshot device))))
          (finally (session/close! device)))))))

(deftest dedicated-temporary-button-does-not-enable-fine-adjustment
  (doseq [mode [:poly-aftertouch :mpe]]
    (testing (name mode)
      (let [views (atom [])
            display {:device :push-3 :input :view :open! (constantly :capture-display)
                     :render! (fn [_ view] (swap! views conj view)) :close! (fn [_])}
            settings (cond-> {:expression-mode mode :cue-gestures? true :display display
                              :temporary-encoder-modifier :right :operator-gestures? true
                              :button-bindings {:blackout :shift :right :page-right}
                              :authority {:operator-id :push-3-test}}
                       (= :mpe mode) (assoc :zone {:manager-channel 0 :member-channels [1]}
                                            :mpe-note-cells {40 [0 0]}))
            {:keys [show receive device]} (harness settings)
            level #(get-in @show [:instances "0:1" :params :level])]
        (try
          (swap! show assoc :rig {:fixtures [{:id :light :channels {:pan [1 2]}}]})
          (swap! show assoc-in [:registry :effects :wash :outputs] {:pan {:op :param :key :level}})
          (swap! show launch-test-wash)
          (session/open! device)
          (@receive [0xb4 23 127])
          (is (false? (:fine? (peek @views))))
          (@receive [0x92 9 127])
          (@receive [0xb2 19 1])
          (is (= 0.51 (level)))
          (@receive [0x82 9 0])
          (is (= 0.5 (level)))
          (@receive [0xb4 22 127])
          (is (true? (:fine? (peek @views))))
          (@receive [0xb4 23 0])
          (is (true? (:fine? (peek @views))))
          (@receive [0xb4 22 0])
          (is (false? (:fine? (peek @views))))
          (is (empty? (:errors (session/snapshot device))))
          (finally (session/close! device)))))))

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

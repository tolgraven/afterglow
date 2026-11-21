(ns afterglow.control.devices.push-2-test
  (:require [clojure.test :refer [deftest is]]
            [afterglow.control.devices.session :as session]
            [afterglow.control.devices.session-test :as fixture]
            [afterglow.control.devices.push-2 :as push]
            [afterglow.control.codecs.push-2 :as codec]
            [afterglow.control.model :as model]))

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

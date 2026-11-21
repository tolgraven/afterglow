(ns afterglow.control.devices.push-2-test
  (:require [clojure.test :refer [deftest is]]
            [afterglow.control.devices.session :as session]
            [afterglow.control.devices.session-test :as fixture]
            [afterglow.control.devices.push-2 :as push]
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
(defn harness []
  (let [h (fixture/harness)]
    (swap! (:show h) assoc-in [:registry :effects :wash :params] schemas)
    (swap! (:show h) assoc-in [:registry :effects :wash :param-order] order)
    (fixture/ready! h)))
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

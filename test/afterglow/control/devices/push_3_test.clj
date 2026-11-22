(ns afterglow.control.devices.push-3-test
  (:require [clojure.test :refer [deftest is]]
            [afterglow.control.model :as model]
            [afterglow.control.devices.push-3 :as push]
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

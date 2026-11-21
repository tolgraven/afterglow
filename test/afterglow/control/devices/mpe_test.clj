(ns afterglow.control.devices.mpe-test
  (:require [clojure.test :refer [deftest is]]
            [afterglow.control.model :as model]
            [afterglow.control.devices.expressive :as expressive]
            [afterglow.control.devices.mpe :as mpe]
            [afterglow.control.devices.seaboard :as seaboard]
            [afterglow.control.devices.push-3 :as push]
            [afterglow.control.devices.session :as session]))

(def schemas
  {:level {:type :number :default 0.5 :bounds [0 1] :control/axis :pressure}
   :pan {:type :number :default 0.0 :bounds [-180 180] :control/axis :glide}
   :step {:type :integer :default 3 :bounds [1 5] :control/axis :slide}
   :enabled {:type :boolean :default false :control/axis :strike}
   :mode {:type :enum :default :low :values [:low :mid :high] :control/axis :lift}})
(def options {:zone {:manager-channel 0 :member-channels [1 2 3]} :cue-id :expressive
              :axes #{:strike :pressure :glide :slide :lift}})

(defn show [] (model/new-show {:registry {:effects {:wash {:id :wash :version 1 :params schemas}}
                                       :cues {:expressive {:id :expressive :version 1 :effect-id :wash}}}
                             :pages {:main {:id :main :cells {[0 0] :expressive}}}}))

(defn harness [profile]
  (let [db (atom (show)) receive (atom nil) commands (atom [])
        device (session/create {:session-id "mpe-test" :profile profile :now-ms! (constantly 0) :model! #(deref db)
                                :dispatch! (fn [command] (let [r (model/apply-command @db command)]
                                                          (swap! commands conj command) (reset! db (:model r)) r))
                                :midi {:open! #(do (reset! receive %) :midi)
                                       :send! (fn [_ _] (throw (ex-info "Unexpected output" {})))
                                       :close! (fn [_])}})]
    {:db db :receive receive :commands commands :device device}))

(deftest schema-plan-maps-bounded-and-discrete-values-and-reports-limits
  (let [plan (expressive/plan schemas #{:strike :pressure :glide :slide :lift})]
    (is (= {:level 1.0 :pan 0.0 :step 5 :enabled true :mode :mid}
           (expressive/values plan {:pressure 1 :glide 0 :slide 1 :strike 0.8 :lift 0.5})))
    (is (= {:pan -180.0 :step 1 :enabled false} (expressive/values plan {:glide -5 :slide -1 :strike 0.1}))))
  (let [plan (expressive/plan (assoc schemas :unbounded {:type :number :default 0 :control/axis :slide}
                                  :color {:type :color :default [0 0 0] :control/axis :pressure}
                                  :focus {:type :number :default 0 :bounds [0 1]})
                              #{:pressure :slide} {:level nil})]
    (is (= [:level] (:disabled plan)))
    (is (= #{:unavailable-axis :unsupported-schema} (set (map :code (:diagnostics plan)))))
    (is (= [{:param :focus :axis :slide :reason :conventional-parameter-name :requires-confirmation? true}] (:suggestions plan)))
    (is (not (contains? (expressive/values plan {:slide 1 :pressure 1}) :focus)))))

(deftest actual-seaboard-session-keeps-same-pitch-on-two-channels-independent
  (let [{:keys [db receive device]} (harness (seaboard/profile options))]
    (try
      (session/open! device)
      (@receive [0x91 60 127])
      (let [a (get-in (session/snapshot device) [:local :selected-instance])]
        (@receive [0x92 60 64])
        (let [b (get-in (session/snapshot device) [:local :selected-instance])]
          (is (not= a b))
          (is (= :seaboard-m (get-in @db [:instances a :source :adapter])))
          (@receive [0xd1 127]) (@receive [0xe2 127 127]) (@receive [0xb2 74 127])
          (is (= 1.0 (get-in @db [:instances a :params :level])))
          (is (= 0.0 (get-in @db [:instances b :params :level])))
          (is (= 0.0 (get-in @db [:instances a :params :pan])))
          (is (= 180.0 (get-in @db [:instances b :params :pan])))
          (is (= 5 (get-in @db [:instances b :params :step])))
          (@receive [0x81 60 127])
          (is (= :high (get-in @db [:instances a :params :mode])))
          (is (= :releasing (get-in @db [:instances a :phase])))
          (is (= :running (get-in @db [:instances b :phase])))
          (session/suspend! device)
          (is (= :releasing (get-in @db [:instances b :phase])))))
      (is (= [] (:errors (session/snapshot device))))
      (finally (session/close! device)))))

(deftest delayed-ack-keeps-lift-before-release-and-rejects-failed-launches
  (let [profile (mpe/profile options) db (show)
        press ((:input profile) (:initial-state profile) [0x91 60 127] db {:command-id "press"})
        bend ((:input profile) (:state press) [0xe1 127 127] db {:command-id "bend"})
        end ((:input profile) (:state bend) [0x81 60 127] db {:command-id "release"})
        launch (first (:commands press))
        ack ((:ack profile) (:state end) launch {:status :accepted :instance-id "a"})
        rejected ((:ack profile) (:state press) launch {:status :rejected})]
    (is (= [] (:commands end)))
    (is (= [:param/set :param/set :instance/end] (mapv :op (:commands ack))))
    (is (= [:mode :pan] (mapv :param (take 2 (:commands ack)))))
    (is (= {} (get-in ack [:state :voices])))
    (is (= {} (get-in ack [:state :holds :gestures])))
    (is (= {} (get-in rejected [:state :voices])))
    (is (= [] (:commands rejected)))))

(deftest push-3-mpe-uses-captured-note-cells-with-rotating-channels
  (let [profile (push/profile {:user-mode? true :expression-mode :mpe :zone (:zone options)
                               :layout {} :mpe-note-cells {40 [0 0]}})
        {:keys [db receive device]} (harness profile)]
    (try
      (session/open! device)
      (@receive [0x91 40 127]) (@receive [0x92 40 127])
      (is (= 2 (count (:instances @db))))
      (@receive [0xe1 0 0]) (@receive [0xb2 74 127])
      (let [[a b] (sort-by :order (vals (:instances @db)))]
        (is (= -180.0 (get-in a [:params :pan])))
        (is (= 0.0 (get-in b [:params :pan])))
        (is (= 5 (get-in b [:params :step])))
        (is (= :push-3 (get-in b [:source :adapter])))
        (@receive [0x81 40 0])
        (is (= :running (get-in @db [:instances (:id b) :phase]))))
      (is (= [] (:errors (session/snapshot device))))
      (finally (session/close! device)))))

(deftest pinned-cues-use-the-captured-version-parameter-schema
  (let [old {:id :wash :version 1 :params (assoc-in schemas [:pan :bounds] [-10 10])}
        db (-> (show) (assoc-in [:registry :effects :wash :version] 2)
               (assoc-in [:registry :versions [:effects :wash 1]] old)
               (assoc-in [:registry :cues :expressive :effect-version] 1))
        profile (mpe/profile options)
        before ((:input profile) (:initial-state profile) [0xe1 127 127] db {:command-id "bend"})
        launch ((:input profile) (:state before) [0x91 60 127] db {:command-id "press"})]
    (is (= 10.0 (get-in launch [:commands 0 :launch :params :pan])))))

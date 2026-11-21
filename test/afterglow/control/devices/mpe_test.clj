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
    (is (= :automatic (:origin (first (filter #(= :focus (:param %)) (:mappings plan))))))
    (is (= 1.0 (:focus (expressive/values plan {:slide 1 :pressure 1}))))
    (is (empty? (:mappings (expressive/plan {:focus {:type :number :default 0 :bounds [0 1]}}
                                           #{:slide} {} {:auto? false}))))))

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

(deftest automatic-mapping-and-explicit-component-ranges-are-type-safe
  (let [schemas {:intensity {:type :number :default 0.5 :bounds [0 1]}
                 :horizontal {:type :number :default 0 :bounds [-90 90] :control/semantic :pan}
                 :choice {:type :enum :default :sine :values [:sine :triangle :square]}
                 :gate {:type :boolean :default false}
                 :count {:type :integer :default 2 :bounds [1 5]}
                 :color {:type :color :default [0.2 0.3 0.4]}
                 :position {:type :vector :size 3 :default [0 0 2] :bounds [-10 10]}
                 :window {:type :range :default [2 8] :bounds [0 10]}}
        overrides {:intensity {:axis :pressure :range [0.2 0.6] :curve :ease-in :inverted? true}
                   :choice :slide :gate :strike :count {:axis :slide :range [2 4]}
                   :color {:axis :pressure :component 1}
                   :position [{:axis :glide :component 0} {:axis :slide :component 1 :range [1 5]}]
                   :window {:axis :pressure :component 0}}
        plan (expressive/plan schemas (keys afterglow.control.codecs.mpe/axes) overrides)
        values (expressive/values plan {:pressure 0.5 :glide -1 :slide 1 :strike 0.1}
                                  {:color [0.8 0.1 0.6] :position [2 3 4] :window [2 3]})]
    (is (empty? (:diagnostics plan)))
    (is (< (Math/abs (- 0.3 (:intensity values))) 1.0e-12))
    (is (= {:horizontal -90.0 :choice :square :gate false :count 4
            :color [0.8 0.5 0.6] :position [-10.0 5.0 4] :window [3 3]}
           (dissoc values :intensity)))
    (is (= :explicit (:origin (first (filter #(= :intensity (:param %)) (:mappings plan))))))
    (doseq [input [0 0.1 0.5 0.9 1]]
      (is (every? (fn [[param value]] (afterglow.control.params/valid-value? (get schemas param) value))
                  (expressive/values plan {:pressure input :slide input :glide (- (* 2 input) 1) :strike input}))))))

(deftest invalid-and-disabled-mappings-never-produce-parameter-values
  (doseq [policy [{:enabled? "false"} {:auto? 0} {:disabled-axes [:unknown]}
                  {:params {:level {:axis :pressure :curve :unknown}}}
                  {:params {:level {:axis :pressure :range [0 ##NaN]}}}
                  {:params {:level {:axis :pressure :input-range [1 0]}}}
                  {:cues {:one {:cues {}}}}]]
    (is (thrown? clojure.lang.ExceptionInfo (expressive/normalize-policy policy))))
  (let [plan (expressive/plan schemas #{:pressure :glide :slide}
                              {:level {:axis :pressure :range [0 2]} :pan nil :step {:axis :slide :range [2.1 2.9]}})]
    (is (= #{:invalid-range :unavailable-axis} (set (map :code (:diagnostics plan)))))
    (is (= {} (expressive/values plan {:pressure 1 :glide 1 :slide 1}))))
  (is (= {} (expressive/values (expressive/plan schemas (keys afterglow.control.codecs.mpe/axes) {} {:enabled? false})
                              {:pressure 1 :glide 1 :slide 1 :strike 1 :lift 1}))))

(deftest portable-policy-normalizes-json-axis-names-and-preserves-precedence
  (let [config (expressive/normalize-config
                 {:devices {:controller {:auto? false :disabled-axes ["glide"]
                                         :params {:level {:axis "pressure" :curve "smoothstep"}}
                                         :cues {:expressive {:auto? true :params {:level nil :step {:axis "slide"}}}}}}})
        policy (expressive/policy {:settings {:expressive config}} "controller" "expressive" {})]
    (is (= #{:glide} (:disabled-axes policy)))
    (is (true? (:auto? policy)))
    (is (= {:level nil :step {:axis :slide}} (:params policy)))
    (is (false? (:enabled? (expressive/policy {:settings {:expressive (assoc-in config [:devices :controller :enabled?] false)}}
                                             "controller" :expressive {:enabled? true}))))))

(deftest push-mpe-live-policy-disable-and-overrides-retain-owned-release
  (let [profile (push/profile {:user-mode? true :expression-mode :mpe :zone (:zone options)
                               :layout {} :mpe-note-cells {40 [0 0]} :mapping-id "push-main"})
        {:keys [db receive device]} (harness profile)]
    (try
      (session/open! device)
      (@receive [0x91 40 127])
      (let [id (get-in (session/snapshot device) [:local :mpe :selected-instance])]
        (@receive [0xd1 127])
        (is (= 1.0 (get-in @db [:instances id :params :level])))
        (swap! db assoc-in [:settings :expressive :devices :push-main]
               {:params {:level {:axis :slide :range [0.2 0.8]} :pan nil}
                :disabled-axes #{:pressure}})
        (@receive [0xd1 0]) (@receive [0xe1 127 127])
        (is (= 1.0 (get-in @db [:instances id :params :level])))
        (is (= 0.0 (get-in @db [:instances id :params :pan])))
        (@receive [0xb1 74 127])
        (is (= 0.8 (get-in @db [:instances id :params :level])))
        (swap! db assoc-in [:settings :expressive :devices :push-main :cues :expressive] {:enabled? false})
        (@receive [0xb1 74 0])
        (is (= 0.8 (get-in @db [:instances id :params :level])))
        (@receive [0x81 40 127])
        (is (= :releasing (get-in @db [:instances id :phase])))
        (is (empty? (get-in (session/snapshot device) [:local :mpe :voices]))))
      (is (empty? (:errors (session/snapshot device))))
      (finally (session/close! device)))))

(deftest unannotated-auto-mapping-can-be-disabled-without-disabling-cues
  (let [{:keys [db receive device]} (harness (seaboard/profile (assoc options :mapping-id :roli)))
        unannotated (into {} (map (fn [[id schema]] [id (dissoc schema :control/axis)]) schemas))]
    (swap! db assoc-in [:registry :effects :wash :params] unannotated)
    (try
      (session/open! device)
      (@receive [0x91 60 127])
      (let [a (get-in (session/snapshot device) [:local :selected-instance])]
        (@receive [0xd1 127])
        (is (= 1.0 (get-in @db [:instances a :params :level])))
        (swap! db assoc-in [:settings :expressive :devices :roli] {:enabled? false})
        (@receive [0x92 62 64])
        (let [b (get-in (session/snapshot device) [:local :selected-instance])]
          (is (= 2 (count (:instances @db))))
          (is (= 0.5 (get-in @db [:instances b :params :level])))
          (@receive [0xd1 0]) (@receive [0xd2 127])
          (is (= 1.0 (get-in @db [:instances a :params :level])))
          (is (= 0.5 (get-in @db [:instances b :params :level])))
          (@receive [0x81 60 0]) (@receive [0x82 62 0])
          (is (every? #(= :releasing (:phase %)) (vals (:instances @db))))))
      (is (empty? (:errors (session/snapshot device))))
      (finally (session/close! device)))))

(deftest active-expression-uses-instance-schema-and-preserves-other-components
  (let [{:keys [db receive device]} (harness (seaboard/profile options))]
    (try
      (session/open! device)
      (@receive [0x91 60 127])
      (let [id (get-in (session/snapshot device) [:local :selected-instance])]
        ;; A registry edit alone cannot change the captured instance schema.
        (swap! db assoc-in [:registry :effects :wash :params :level :bounds] [0 100])
        (@receive [0xd1 127])
        (is (= 1.0 (get-in @db [:instances id :params :level])))
        ;; A successful hot reload publishes a new captured definition.
        (swap! db assoc-in [:instances id :definition :params :level :bounds] [0 10])
        (@receive [0xd1 127])
        (is (= 10.0 (get-in @db [:instances id :params :level])))
        (swap! db assoc-in [:instances id :definition :params :color]
               {:type :color :default [0 0 0]})
        (swap! db assoc-in [:instances id :params :color] [0.2 0.3 0.4])
        (swap! db assoc-in [:settings :expressive :devices "mpe-test" :params]
               {:color {:axis :slide :component 1}})
        (@receive [0xb1 74 127])
        (is (= [0.2 1.0 0.4] (get-in @db [:instances id :params :color]))))
      (finally (session/close! device)))))

(deftest maximally-mapped-retrigger-still-releases-and-launches-within-command-budget
  (let [params (into {} (for [n (range expressive/max-mapped-parameters)]
                          [(keyword (str "lift-" n)) {:type :number :default 0.5 :bounds [0 1] :control/axis :lift}]))
        {:keys [db receive device]} (harness (seaboard/profile options))]
    (try
      (swap! db assoc-in [:registry :effects :wash :params] params)
      (session/open! device)
      (@receive [0x91 60 127])
      (let [first-id (get-in (session/snapshot device) [:local :selected-instance])]
        (@receive [0x91 60 127])
        (let [second-id (get-in (session/snapshot device) [:local :selected-instance])]
          (is (not= first-id second-id))
          (is (= :releasing (get-in @db [:instances first-id :phase])))
          (is (= :running (get-in @db [:instances second-id :phase])))
          (is (empty? (:errors (session/snapshot device))))))
      (finally (session/close! device)))))

(deftest profile-defaults-resolve-nested-cues-before-explicit-cue-options
  (let [defaults (expressive/profile-defaults
                  {:mapping-policy {:enabled? false :disabled-axes #{:glide}
                                    :params {:level :pressure}
                                    :cues {"expressive" {:enabled? true :auto? false :disabled-axes #{:lift}
                                                        :params {:level :slide :step :strike}}}}
                   :param-mappings {:level :strike}
                   :cue-mappings {:expressive {:level :pressure}}} :expressive)]
    (is (false? (:enabled? defaults)))
    (is (false? (:auto? defaults)))
    (is (= #{:glide :lift} (:disabled-axes defaults)))
    (is (= {:level :pressure :step :strike} (:params defaults)))
    (is (not (contains? defaults :cues)))))

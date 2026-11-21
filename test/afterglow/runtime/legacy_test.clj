(ns afterglow.runtime.legacy-test
  (:require [afterglow.runtime.legacy :as bridge]
            [afterglow.channels :as channels]
            [afterglow.effects :as effects]
            [afterglow.effects.dimmer :as dimmer]
            [afterglow.rhythm :as rhythm]
            [afterglow.show :as show]
            [afterglow.show-context :refer [*show* with-show]]
            [afterglow.util :as util]
            [clojure.test :refer [deftest is use-fixtures]]
            [ola-clojure.ola-service :as ola]
            [overtone.at-at :as at-at]))

(use-fixtures :each
  (fn [f]
    (with-show (show/show)
      (f))))

(def definition
  {:id :bridge-test :version 1
   :params {:level {:type :number :default 0.5 :bounds [0 2]}}})

(defn- fixture [native-dimmer?]
  {:name "Context bridge RGB fixture"
   :pan-center 127 :pan-half-circle 85 :tilt-center 127 :tilt-half-circle 85
   :channels (vec (concat [(channels/color 1 :red) (channels/color 2 :green)
                           (channels/color 3 :blue)]
                          (when native-dimmer? [(channels/dimmer 4)])
                          [(channels/fine-channel :pan 5 :fine-offset 6)
                           (channels/fine-channel :tilt 7)
                           (channels/fine-channel :focus 8)
                           (channels/functions :shutter 9 0 "closed" 20 :strobe 221 "open")]))})

(defn- patch! [native-dimmer?]
  (show/patch-fixture! :test (fixture native-dimmer?) 1 1 :x 1 :y 2 :z 3)
  (vec (show/fixtures-named :test)))

(defn- snapshot [instant]
  (rhythm/metro-snapshot (:metronome *show*) instant))

(defn- step
  [context]
  (let [target (get-in context [:frame :fixtures 0 :id])
        instance (:instance context)
        release (if (= :releasing (:phase instance))
                  (- 1.0 (/ (- (get-in context [:frame :time-ms]) (:release-at-ms instance))
                            (:release-duration-ms instance)))
                  1.0)]
    (-> context
        (update-in [:state :frames] (fnil inc 0))
        (assoc :assignments [{:target-id target :attribute :dimmer :value (* release (get-in instance [:params :level]))}
                             {:target-id target :attribute :color :value [1.0 0.25 0.0]}
                             {:target-id target :attribute :pan :value 0.25}
                             {:target-id target :attribute :tilt :value 0.75}
                             {:target-id target :attribute :focus :value 0.2}
                             {:target-id target :attribute :strobe :value 0.5}])
        (update :intents conj {:event :sampled :time-ms (get-in context [:frame :time-ms])}))))

(defn- capture-frame! [instant]
  (let [captured (atom {})
        buffers {1 (byte-array 512)}]
    ;; Use the actual legacy scheduler and resolvers, with its documented serial
    ;; profiling backend. The only output boundary is captured, never transmitted.
    (reset! (:pool *show*) :serial)
    (try
      (with-redefs [ola/UpdateDmxData (fn [request _callback]
                                      (swap! captured assoc (:universe request)
                                             (mapv util/unsign (.toByteArray (:data request)))))
                    at-at/now (constantly instant)]
        (#'show/send-frame *show* buffers (snapshot instant)))
      @captured
      (finally (reset! (:pool *show*) nil)))))

(deftest pure-context-drives-the-actual-legacy-dmx-pipeline
  (let [fixtures (patch! true)
        effect (bridge/effect {:definition definition :step step :fixtures fixtures})]
    (is (instance? afterglow.effects.Effect effect)
        "Existing show/add-effect! requires its concrete Effect record")
    (is (nil? (:instant (bridge/frame-info effect))) "Construction did not evaluate")
    (dimmer/master-set-level (:grand-master *show*) 50)
    (show/add-effect! :context effect)
    (let [bytes (get (capture-frame! 1000) 1)]
      (is (= [255 63 0 64 64 0 191 51 120] (subvec bytes 0 9)))
      (is (every? zero? (subvec bytes 9)))
      (is (= {:frames 1} (:state (bridge/frame-info effect))))
      (is (= [{:event :sampled :time-ms 1000}] (:intents (bridge/frame-info effect)))))
    (is (false? (show/running?)))))

(deftest virtual-dimmer-follows-local-color-and-respects-master
  (let [fixtures (patch! false)
        effect (bridge/effect {:definition definition :step step :fixtures fixtures})]
    (dimmer/master-set-level (:grand-master *show*) 50)
    (show/add-effect! :context effect)
    (is (= [63 15 0] (subvec (get (capture-frame! 1000) 1) 0 3)))
    (is (= {:frames 1} (:state (bridge/frame-info effect))))))

(deftest lifecycle-and-generation-share-a-single-evaluation
  (let [effect (bridge/effect {:definition definition :step step :fixtures (patch! true)})
        frame (snapshot 1000)]
    (is (true? (effects/still-active? effect *show* frame)))
    (let [assigners (effects/generate effect *show* frame)]
      (is (identical? assigners (effects/generate effect *show* frame)))
      (bridge/set-params! effect {:level 0.25})
      (is (identical? assigners (effects/generate effect *show* frame))))
    (is (= {:frames 1} (:state (bridge/frame-info effect))))
    (effects/generate effect *show* (snapshot 1020))
    (is (= {:frames 2} (:state (bridge/frame-info effect))))
    (is (= 0.25 (get-in (bridge/frame-info effect) [:params :level])))))

(deftest concurrent-legacy-calls-do-not-double-step
  (let [calls (atom 0)
        effect (bridge/effect {:definition definition :fixtures (patch! true)
                               :step (fn [context] (swap! calls inc) (step context))})
        frame (snapshot 1000)
        gate (promise)
        jobs (mapv (fn [n] (future @gate
                                   (if (even? n) (effects/still-active? effect *show* frame)
                                       (count (effects/generate effect *show* frame))))) (range 16))]
    (try
      (deliver gate true)
      (is (not-any? #{:timeout} (mapv #(deref % 2000 :timeout) jobs)))
      (is (= 1 @calls))
      (is (= {:frames 1} (:state (bridge/frame-info effect))))
      (finally (doseq [job jobs] (future-cancel job))))))

(deftest timed-release-is-visible-to-the-pure-step-and-then-removes
  (let [effect (bridge/effect {:definition definition :step step :fixtures (patch! true)
                               :duration-ms 100 :release-duration-ms 50})]
    (is (effects/still-active? effect *show* (snapshot 1000)))
    (is (effects/still-active? effect *show* (snapshot 1125)))
    (is (= :releasing (:phase (bridge/frame-info effect))))
    (is (= 6 (count (effects/generate effect *show* (snapshot 1125)))))
    (is (false? (effects/still-active? effect *show* (snapshot 1150))))
    (is (= [] (effects/generate effect *show* (snapshot 1150))))
    (is (= {:frames 2} (:state (bridge/frame-info effect))))))

(deftest explicit-end-and-reset-own-their-lifecycle
  (let [effect (bridge/effect {:definition definition :step step :fixtures (patch! true)
                               :release-duration-ms 50})]
    (effects/generate effect *show* (snapshot 1000))
    (is (false? (effects/end effect *show* (snapshot 1010))))
    (is (effects/still-active? effect *show* (snapshot 1030)))
    (is (false? (effects/still-active? effect *show* (snapshot 1060))))
    (bridge/reset-effect! effect {:state {:frames 10} :params {:level 0.2} :started-at-ms 2000})
    (is (= 1 (:generation (bridge/frame-info effect))))
    (effects/generate effect *show* (snapshot 2000))
    (is (= {:frames 11} (:state (bridge/frame-info effect))))
    (is (= 0.2 (get-in (bridge/frame-info effect) [:params :level])))))

(deftest terminal-step-retains-one-final-frame
  (let [effect (bridge/effect {:definition definition :fixtures (patch! true)
                               :step (comp #(assoc % :done? true) step)})]
    (is (effects/still-active? effect *show* (snapshot 1000)))
    (is (seq (effects/generate effect *show* (snapshot 1000))))
    (is (false? (effects/still-active? effect *show* (snapshot 1020))))
    (is (= [] (effects/generate effect *show* (snapshot 1020))))))

(deftest definition-duration-is-a-one-shot-default-not-an-implicit-expiry
  (let [fixtures (patch! true)
        definition (assoc definition :duration-ms 10)
        persistent (bridge/effect {:definition definition :fixtures fixtures :step step})
        once (bridge/effect {:definition definition :fixtures fixtures :step step :mode :one-shot})]
    (effects/generate persistent *show* (snapshot 1000))
    (effects/generate once *show* (snapshot 1000))
    (is (effects/still-active? persistent *show* (snapshot 1020)))
    (is (false? (effects/still-active? once *show* (snapshot 1020))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (bridge/effect {:definition (dissoc definition :duration-ms) :fixtures fixtures
                                 :step step :mode :one-shot})))))

(deftest normalized-functions-do-not-accidentally-use-physical-unit-scalers
  (let [raw (assoc (fixture true) :channels
                   [(channels/functions :shutter 1 0 "closed"
                                         20 {:type :strobe :scale-fn (fn [hz] (* hz 10))}
                                         221 "open")])]
    (show/patch-fixture! :scaled raw 1 1)
    (let [fixtures (vec (show/fixtures-named :scaled))
          make-step (fn [blend]
                      (fn [context]
                        (assoc context :assignments
                               [{:target-id (get-in context [:frame :fixtures 0 :id])
                                 :attribute :strobe :value 0.5 :blend blend}])))
          effect (bridge/effect {:definition definition :fixtures fixtures :step (make-step :replace)})
          ambiguous (bridge/effect {:definition definition :fixtures fixtures :step (make-step :max)})]
      (show/add-effect! :scaled effect)
      (is (= 120 (first (get (capture-frame! 1000) 1))))
      (is (thrown? clojure.lang.ExceptionInfo
                   (effects/generate ambiguous *show* (snapshot 1000))))
      (is (nil? (:instant (bridge/frame-info ambiguous)))))))

(deftest invalid-output-does-not-commit-state-and-can-be-repaired
  (let [effect (bridge/effect {:definition definition :fixtures (patch! true)
                               :params {:level 2} :step step})]
    (is (thrown? clojure.lang.ExceptionInfo (effects/generate effect *show* (snapshot 1000))))
    (is (= {} (:state (bridge/frame-info effect))))
    (is (nil? (:instant (bridge/frame-info effect))))
    (bridge/set-params! effect {:level 0.5})
    (is (seq (effects/generate effect *show* (snapshot 1000))))
    (is (= {:frames 1} (:state (bridge/frame-info effect))))))

(deftest bridges-cannot-share-lifecycle-across-shows-or-rewind-frames
  (let [effect (bridge/effect {:definition definition :fixtures (patch! true) :step step})]
    (effects/generate effect *show* (snapshot 1000))
    (is (thrown? clojure.lang.ExceptionInfo
                 (effects/generate effect (assoc *show* :id :other) (snapshot 1000))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (effects/generate effect *show* (snapshot 999))))))

(deftest pure-step-does-not-receive-legacy-mutable-geometry
  (let [seen (atom nil)
        effect (bridge/effect {:definition definition :fixtures (patch! true)
                               :step (fn [context] (reset! seen context) context)})]
    (effects/generate effect *show* (snapshot 1000))
    (is (= [1.0 2.0 3.0] (get-in @seen [:frame :fixtures 0 :position])))
    (is (= #{:id :name :position} (set (keys (get-in @seen [:frame :fixtures 0])))))
    (is (= 1000 (get-in @seen [:frame :time-ms])))
    (is (not (contains? @seen :show)))))

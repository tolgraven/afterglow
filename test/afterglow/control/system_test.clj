(ns afterglow.control.system-test
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.edn :as edn]
            [afterglow.control.model :as model]
            [afterglow.control.system :as system]
            [afterglow.runtime :as runtime]
            [afterglow.runtime.engine :as engine]
            [afterglow.runtime.executor :as executor]
            [afterglow.render.frame :as frame]))

(def fixture {:id :lamp :universe 1 :address 1 :channels {:dimmer 1}})
(defn apply! [show payload]
  (let [result (model/apply-command show
                 (merge {:command-id (str (:revision show)) :source :test :show-id (:show-id show)
                         :epoch (:epoch show) :time-ms (:time-ms show)} payload))]
    (when-not (= :accepted (get-in result [:ack :status])) (throw (ex-info "Rejected test command" (:ack result))))
    (:model result)))
(defn launched [options]
  (let [definition {:id :light :version 1 :params {:level {:type :number :default 0.8 :bounds [0 1]}}
                    :outputs {:dimmer {:op :param :key :level}}}]
    (-> (model/new-show {:registry {:effects {:light definition} :cues {:light {:id :light :version 1 :effect-id :light}}}})
        (apply! {:op :cue/launch :cue-id :light :launch options}))))
(defn compiler [_]
  (fn [context]
    (-> context
        (update-in [:state :steps] (fnil inc 0))
        (update :assignments conj {:target-id :lamp :attribute :dimmer :value (get-in context [:instance :params :level])})
        (update :intents conj {:type :observed :state (:state context) :frame (select-keys (:frame context) [:time-ms :beat :number :delta-ms])})
        ;; Like the ordinary declarative compiler without an authored envelope.
        (assoc :done? (= :releasing (get-in context [:instance :phase]))))))
(defn advance [show ms beat]
  (engine/advance (assoc-in show [:transport :beat] beat) {:time-ms ms :fixtures [fixture]} compiler))
(defn opacity [result] (:opacity (first (:assignments result)) 1.0))
(defn render-bytes [result]
  (let [rendered (frame/resolve-contributions [fixture] (:contributions result))]
    (mapv #(bit-and 255 %) (get-in rendered [:universes 1]))))

(deftest opacity-is-independent-and-toggle-remembers-the-last-nonzero-level
  (let [show (launched {})
        changed (apply! show {:op :instance/opacity-set :instance-id "0:1" :value 0.25})
        off (apply! changed {:op :instance/opacity-toggle :instance-id "0:1"})
        on (apply! off {:op :instance/opacity-toggle :instance-id "0:1"})]
    (is (= {:level 0.8} (get-in on [:instances "0:1" :params])))
    (is (= 0.25 (get-in on [:instances "0:1" :system :opacity])))
    (is (= 51 (first (render-bytes (advance changed 0 0)))))
    (is (= [] (:contributions (advance off 0 0))))
    (is (= {:steps 1} (get-in (advance off 0 0) [:model :instances "0:1" :state])))))

(deftest pause-freezes-state-clock-and-intents-while-manual-params-remain-live
  (let [first-frame (advance (launched {}) 100 1)
        paused (apply! (:model first-frame) {:op :instance/pause :instance-id "0:1"})
        held (advance paused 5000 20)
        changed (apply! (:model held) {:op :param/set :instance-id "0:1" :param :level :value 0.4})
        changed-frame (advance changed 7000 30)
        resumed (apply! (:model changed-frame) {:op :instance/resume :instance-id "0:1"})
        next-frame (advance resumed 7100 31)]
    (is (= (:assignments first-frame) (:assignments held)))
    (is (= {:steps 1} (get-in held [:model :instances "0:1" :state])))
    (is (= [] (:intents held)))
    (is (= 0.4 (-> changed-frame :assignments first :value)))
    (is (= {:steps 1} (get-in changed-frame [:model :instances "0:1" :state])))
    (is (= {:steps 2} (get-in next-frame [:model :instances "0:1" :state])))
    (is (= {:time-ms 200 :beat 2 :number 2 :delta-ms 100} (-> next-frame :intents first :frame)))
    (is (= (:model held) (edn/read-string (pr-str (:model held)))) "No typed output buffers enter model state")))

(deftest pause-freezes-musical-and-millisecond-expiry-and-end-resumes-release
  (doseq [duration [{:beats 2} {:ms 200}]]
    (let [first-frame (advance (launched {:mode :one-shot :duration duration :system {:release {:beats 1}}}) 100 1)
          paused (apply! (:model first-frame) {:op :instance/pause :instance-id "0:1"})
          held (advance paused 5000 50)
          ended (apply! (:model held) {:op :instance/end :instance-id "0:1"})
          releasing (advance ended 5050 50.5)
          done (advance (:model releasing) 5100 51)]
      (is (= :running (get-in held [:model :instances "0:1" :phase])))
      (is (false? (get-in ended [:instances "0:1" :system :paused?])))
      (is (= :releasing (get-in releasing [:model :instances "0:1" :phase])))
      (is (= 0.5 (opacity releasing)))
      (is (= {} (get-in done [:model :instances]))))))

(deftest attack-release-is-musical-independent-and-continuous-when-edited
  (let [show (launched {:system {:attack {:beats 2} :release {:beats 2}}})
        zero (advance show 0 0)
        half (advance (:model zero) 500 1)
        edited (apply! (:model half) {:op :instance/envelope-set :instance-id "0:1" :envelope {:attack {:beats 1}}})
        same (advance edited 500 1)
        full (advance (:model same) 2000 2)
        ended (apply! (:model full) {:op :instance/end :instance-id "0:1"})
        tail (advance ended 2500 3)
        extended (apply! (:model tail) {:op :instance/envelope-set :instance-id "0:1" :envelope {:release {:beats 2}}})
        same-tail (advance extended 2500 3)
        last-tail (advance (:model same-tail) 4000 4)
        done (advance (:model last-tail) 5000 5)]
    (is (= [] (:assignments zero)))
    (is (= 0.5 (opacity half) (opacity same)))
    (is (= 1.0 (opacity full)))
    (is (= 0.5 (opacity tail) (opacity same-tail)))
    (is (= 0.25 (opacity last-tail)))
    (is (= :releasing (get-in tail [:model :instances "0:1" :phase])))
    (is (= {} (get-in done [:model :instances])))
    (is (= [] (:contributions done)))))

(deftest typed-buffers-regenerate-while-paused-and-worker-completion-order-does-not-matter
  (let [show (-> (launched {}) (apply! {:op :cue/launch :cue-id :light :launch {:system {:opacity 0.5}}}))
        batch-compiler (fn [_] (fn [context]
                                (-> context
                                    (update-in [:state :steps] (fnil inc 0))
                                    (runtime/append-contributions
                                     [{:kind :batch :batch {:target-ids [:lamp] :blend :max
                                                           :outputs {:dimmer {:type :number :components 1 :values (double-array [0.6])}}}}]))))
        advance* #(engine/advance %1 {:time-ms %2 :fixtures [fixture]} batch-compiler)
        first-frame (advance* show 100)
        paused (apply! (:model first-frame) {:op :group/apply :selector {} :action {:op :instance/pause}})
        held (advance* paused 1000)
        before (get-in first-frame [:contributions 0 :batch :outputs :dimmer :values])
        after (get-in held [:contributions 0 :batch :outputs :dimmer :values])]
    (is (not (identical? before after)))
    (is (= (vec before) (vec after)))
    (is (= (:model held) (edn/read-string (pr-str (:model held)))))
    (with-open [^java.io.Closeable pool (executor/create {:workers 2 :queue-size 2 :timeout-ms 1000})]
      (let [threaded (engine/advance paused {:time-ms 1000 :fixtures [fixture]} batch-compiler
                                    (fn [f xs] (reverse ((executor/mapper pool) f xs))))]
        (is (= (:model held) (:model threaded)))
        (is (= (render-bytes held) (render-bytes threaded)))))))

(deftest system-validation-rejects-invalid-control-and-captured-state
  (doseq [options [nil [] {:opacity Double/NaN} {:opacity -1} {:attack {:beats -1}} {:release {:beats 1 :ms 1}} {:other 1}]]
    (is (thrown? clojure.lang.ExceptionInfo (system/validate-options options))))
  (doseq [system [{:opacity 2} {:paused? true} {:paused? :yes}
                  {:clock-offset-ms Double/NaN} {:gate {:kind :wrong}}]]
    (is (thrown? clojure.lang.ExceptionInfo (system/validate-state {:system system}))))
  (let [show (launched {})]
    (doseq [options [[] nil {:opacity 4}]]
      (let [result (model/apply-command show {:op :cue/launch :cue-id :light :launch {:system options}
                                            :command-id :bad :source :test :show-id :main :epoch 0 :time-ms 0})]
        (is (= :rejected (get-in result [:ack :status])))
        (is (identical? show (:model result)))))))

(deftest paused-reload-waits-until-resume-and-restart-clears-frozen-input
  (let [show (launched {:reload-policy :restart :system {:attack {:beats 2}}})
        first-frame (advance show 100 1)
        paused (apply! (:model first-frame) {:op :instance/pause :instance-id "0:1"})
        updated (apply! paused {:op :registry/publish :kind :effects
                               :definition (-> (get-in paused [:registry :effects :light])
                                               (assoc :version 2 :initial-state {:steps 20}))})
        held (advance updated 5000 30)
        resumed (apply! (:model held) {:op :instance/resume :instance-id "0:1"})
        fresh (advance resumed 5100 31)]
    (is (= 1 (get-in held [:model :instances "0:1" :effect-version])))
    (is (= [] (:intents held)))
    (is (= 2 (get-in fresh [:model :instances "0:1" :effect-version])))
    (is (= {:steps 21} (get-in fresh [:model :instances "0:1" :state])))
    (is (= {:steps 20} (get-in fresh [:model :instances "0:1" :system :last-input-state])))
    (is (= [] (:assignments fresh)) "Restart begins the independent attack at zero")))

(deftest paused-or-hidden-effects-cannot-hide-invalid-step-results
  (let [show (-> (launched {:system {:opacity 0}})
                 (apply! {:op :instance/pause :instance-id "0:1"}))]
    (doseq [invalid [#(dissoc % :state) #(assoc % :done? :yes)
                     #(assoc % :contributions [{:kind :invalid}])]]
      (is (thrown? clojure.lang.ExceptionInfo
                   (engine/advance show {:time-ms 100} (fn [_] invalid)))))))

(deftest default-system-opacity-preserves-ordinary-and-typed-contribution-shapes
  (let [result (advance (launched {}) 0 0)]
    (is (= [{:target-id :lamp :attribute :dimmer :value 0.8}] (:assignments result)))
    (is (= [{:kind :assignments :assignments [{:target-id :lamp :attribute :dimmer :value 0.8}]}]
           (:contributions result)))))

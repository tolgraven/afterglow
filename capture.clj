(require '[afterglow.control.model :as control]
         '[clojure.pprint :as pprint]
         '[tolglow.show :as show])

(def definition {:id :dimmer :version 1 :params {} :targets [:open] :outputs {:dimmer 1}})

(def fixtures [{:id :open :universe 1 :address 1 :channels {:dimmer 1}}
               {:id :muted :universe 1 :address 2 :channels {:dimmer 1}}])

(defn capture [policy batch?]
  (let [model (control/new-show {:show-id :effect-group-reload-capture :rig {:fixtures fixtures}
                                 :registry {:effects {:dimmer definition}
                                            :cues {:dimmer {:id :dimmer :version 1 :effect-id :dimmer}}}})
        runtime (show/create-runtime {:model model :batch? batch? :workspace-options nil
                                       :workers 2 :effect-log! (fn [_])})
        publish (fn [version targets]
                  {:op :registry/publish :kind :effects
                   :definition (assoc definition :version version :targets targets)})
        bad (update (publish 3 [:open]) :definition assoc
                    :params {:divisor {:type :number :default 0}}
                    :outputs {:dimmer {:op :divide :args [1 {:op :param :key :divisor}]}})
        source {:adapter :repl :session-id "effect-group-reload-capture"}
        frames [[0 :configure {:op :effect-groups/configure
                               :config {:active-overlay :fixtures
                                        :overlays {:fixtures [{:id :silent :fixture-ids [:muted] :level 0}]}}}]
                [10 :launch {:op :cue/launch :cue-id :dimmer :launch {:reload-policy policy}}]
                [20 :reload-into-mute (publish 2 [:muted])]
                [30 :reject-reload bad]
                [40 :reload-out-of-mute (publish 4 [:open])]]]
    (try
      {:reload-policy policy :batch? batch?
       :frames (mapv (fn [[time label payload]]
                       (let [receipt (show/submit! runtime (assoc payload :source source :command-id (name label)))
                             _ (show/tick! runtime time)
                             ack (deref receipt 1000 {:status :timeout})
                             {:keys [model output status]} @(:state runtime)
                             instance (first (vals (:instances model)))
                             group (first (:instances (show/effect-group-channels runtime)))]
                         (assert (= :accepted (:status ack)) (pr-str ack))
                         (assert (nil? (:error status)) (pr-str status))
                         {:input payload :time-ms time :label label
                          :ack (select-keys ack [:status :revision])
                          :instance (select-keys instance [:id :effect-version :started-at-ms])
                          :reload-fault (select-keys (:reload-fault instance) [:effect-version :stage])
                          :mixer (select-keys group [:overlay-group :member-level])
                          :dmx (mapv #(bit-and % 255) (take 2 (get-in output [:universes 1])))})) frames)}
      (finally (show/stop! runtime)))))

(let [[path tolglow afterglow] *command-line-args*]
  (spit path (with-out-str
               (pprint/pprint {:tolglow tolglow :afterglow afterglow
                               :capture (vec (for [policy [:preserve-state :restart], batch? [false true]]
                                               (capture policy batch?)))}))))

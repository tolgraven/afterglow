(require '[afterglow.control.model :as control]
         '[clojure.data.json :as json]
         '[tolglow.show :as show])

(def nozzle
  {:id :fogger :universe 1 :address 1 :channels {:fog 1}
   :fogger {:flow-m3-min 60 :dmx-range [255 0]}})

(defn show-model [level]
  (control/new-show
   {:rig {:fixtures [nozzle]}
    :registry {:effects {:fog {:id :fog :version 1 :params {} :outputs {:fog level}}}
               :cues {:fog {:id :fog :version 1 :effect-id :fog}}}}))

(defn submit! [runtime time command]
  (let [receipt (show/submit! runtime command)]
    (show/tick! runtime time)
    (let [ack (deref receipt 1000 {})]
      (assert (= :accepted (:status ack)) (pr-str ack)))))

(defn captured-run [batch? native? [label authored-level]]
  (let [runtime (show/create-runtime {:model (show-model authored-level) :batch? batch? :workspace-options nil})]
    (try
      (submit! runtime 0 (cond-> {:op :cue/launch :cue-id :fog}
                           native? (assoc :source {:adapter :repl :native-layer {:id :native :member 0}})))
      (submit! runtime 10 {:op :effect-groups/configure :config {:manual [{:id :fog :cue-ids [:fog]}]}})
      {:batch batch? :native native? :cue label
       :samples (mapv (fn [[time level]]
                       (submit! runtime time {:op :effect-groups/level-set :channel-id [:manual :fog] :value level})
                       (let [{:keys [output status]} @(:state runtime)]
                         (assert (nil? (:error status)) (pr-str status))
                         {:level level
                          :dmx (bit-and 255 (first (get-in output [:universes 1])))}))
                     (map-indexed (fn [index level] [(+ 20 (* 10 index)) level])
                                  [1.0 0.75 0.5 0.25 0.1 0.0]))}
      (finally (show/stop! runtime)))))

(let [[output tolglow-revision afterglow-revision] *command-line-args*
      runs (vec (for [batch? [false true], native? [false true], cue [["off" 1.0] ["full" 0.0]]]
                  (captured-run batch? native? cue)))]
  (spit output (json/write-str {:tolglow tolglow-revision :afterglow afterglow-revision
                                :range [255 0] :runs runs}))
  (println "Captured" (count runs) "headless owner runs."))

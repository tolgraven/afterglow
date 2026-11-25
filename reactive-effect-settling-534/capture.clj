(require '[afterglow.control.model :as control]
         '[afterglow.reactive :as reactive]
         '[afterglow.render.frame :as render]
         '[afterglow.runtime.engine :as engine]
         '[afterglow.runtime.keyframes :as keyframes]
         '[clojure.java.io :as io]
         '[clojure.string :as str])

(defn launch []
  (let [definition {:id :dimmer :version 1 :params {} :layer {:transforms []}}
        cue {:id :dimmer :version 1 :effect-id :dimmer}
        model (control/new-show {:registry {:effects {:dimmer definition} :cues {:dimmer cue}}})
        result (control/apply-command model {:op :cue/launch :cue-id :dimmer :time-ms 0 :source :capture
                                             :command-id "capture-launch" :show-id (:show-id model) :epoch (:epoch model)})]
    (assert (= :accepted (get-in result [:ack :status])))
    (:model result)))

(defn read-field [frame id field]
  (keyframes/inspect (get-in frame [:keyframes id]) :lamp field))

(defn sample-beat [index]
  (if (<= index 88) (/ index 32) (+ 11/4 (- index 88))))

(defn capture! [directory head upstream feature]
  (let [system (reactive/create-system {})
        level (reactive/ratom system :level 0.12)
        computations (atom [])
        fixtures [{:id :lamp :universe 1 :address 1 :channels {:dimmer 1}}]
        patch (render/compile-patch fixtures)
        bindings {:level [:source :level] :profile [:subscription [:profile]]}
        step (keyframes/dependency-driven
              {:inputs [:level :profile] :transition {:beats 1}}
              (fn [{:keys [level profile] :as inputs}]
                (swap! computations conj inputs)
                {:assignments [{:target-id :lamp :attribute :dimmer :value (+ level (:bias profile))}
                               {:target-id :lamp :attribute :beat-ratio :value (:ratio profile)}]}))
        initial (launch)
        instance-id (first (keys (:instances initial)))
        _ (reactive/reg-sub! system :profile (fn [{:keys [db]} _] (select-keys @db [:bias :ratio])))
        {:keys [close!]} (reactive/acquire! system [:profile] (constantly nil))
        columns [:frame :beat :time_ms :event :level :bias :declared_ratio :native_level :preview_level
                 :dmx_slot_1 :native_ratio :target_level :target_ratio :progress :settled :calculations]
        tick (fn [[previous rows] index]
               (let [event (case index 0 "initial" 16 "change" 36 "retarget" 68 "settled" "")
                     _ (case index 16 (reset! level 0.65) 36 (reset! level 0.25) nil)
                     [bias ratio] (cond (< index 16) [0.08 1] (< index 36) [0.25 5] :else [0.10 2])
                     beat (sample-beat index)
                     time-ms (* beat 500)
                     inputs (:inputs (reactive/publish! system {:bias bias :ratio ratio :unrelated index} bindings))
                     model (assoc-in (or (:model previous) initial) [:transport :beat] beat)
                     frame (engine/advance model {:time-ms time-ms :keyframes (:keyframes previous)
                                                  :reactive-inputs inputs :fixtures fixtures} (constantly step))
                     dimmer (read-field frame instance-id :dimmer)
                     native-ratio (read-field frame instance-id :beat-ratio)
                     output (render/resolve-contributions patch (:contributions frame))
                     packed (render/resolve-contributions patch (:contributions frame) {:include-values? false})
                     channel (get-in output [:universes 1])
                     view (get-in output [:values :lamp :dimmer])
                     row (zipmap columns
                                 [index (double beat) (double time-ms) event @level bias ratio
                                  (first (:result dimmer)) view (bit-and 255 (aget ^bytes channel 0))
                                  (first (:result native-ratio)) (first (:target dimmer)) (first (:target native-ratio))
                                  (:progress dimmer) (:settled? dimmer) (count @computations)])]
                 (assert (empty? (:fault-events frame)))
                 (assert (== (:native_level row) view))
                 (assert (java.util.Arrays/equals ^bytes channel ^bytes (get-in packed [:universes 1])))
                 [frame (conj rows row)]))]
    (try
      (let [[_ rows] (reduce tick [nil []] (range 369))
            settled (nth rows 68)
            stable (subvec rows 69)
            proof {:afterglow-head head :released-base upstream :source-commit feature
                   :fixture {:universe 1 :slot 1} :output :in-memory
                   :frames (count rows) :settled-frame (:frame settled) :settled-beat (:beat settled)
                   :last-beat (:beat (peek rows)) :stable-frames (count stable)
                   :stable-elapsed-ms (- (:time_ms (peek rows)) (:time_ms settled))
                   :calculation-frames (mapv :frame (filter #(#{"initial" "change" "retarget"} (:event %)) rows))
                   :calculations (count @computations) :extra-calculations-during-hold 0
                   :settled-preview (:preview_level settled) :settled-dmx-byte (:dmx_slot_1 settled)}]
        (assert (= 300 (count stable)))
        (assert (= 3 (count @computations)))
        (assert (= (:preview_level (nth rows 35)) (:preview_level (nth rows 36))))
        (assert (= (:native_ratio (nth rows 35)) (:native_ratio (nth rows 36))))
        (assert (every? #(= (select-keys settled [:settled :preview_level :dmx_slot_1 :native_ratio :calculations])
                           (select-keys % [:settled :preview_level :dmx_slot_1 :native_ratio :calculations]))
                        stable))
        (spit (io/file directory "trace.csv")
              (str (str/join "," (map name columns)) "\n"
                   (str/join "\n" (map #(str/join "," (map % columns)) rows)) "\n"))
        (spit (io/file directory "proof.edn") (str (pr-str proof) "\n"))
        (spit (io/file directory "pins.txt") (str head "\n" upstream "\n" feature "\n"))
        (prn proof))
      (finally (close!) (reactive/close! system)))))

(apply capture! *command-line-args*)

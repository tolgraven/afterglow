(ns afterglow.control.sensors
  "Pure, composable sensor conditioning and semantic control intent. Adapters own
  permissions, physical sampling, clocks, authentication, packets and publication."
  (:require [afterglow.control.bindings :as bindings]
            [afterglow.control.params :as params]
            [afterglow.time :as time]))

(defn- fail! [message & [details]] (throw (ex-info message {:type ::invalid :details details})))
(defn- finite? [x] (params/finite-number? x))
(defn- id? [x] (or (keyword? x) (and (string? x) (<= 1 (count x) 128))))
(defn- unit? [x] (and (finite? x) (<= 0 x 1)))
(defn- nonnegative? [x] (and (finite? x) (<= 0 x)))
(defn- portable? [x]
  (cond (or (nil? x) (string? x) (keyword? x) (boolean? x)) true
        (number? x) (finite? x)
        (vector? x) (every? portable? x)
        (map? x) (every? (fn [[k v]] (and (or (keyword? k) (string? k)) (portable? v))) x)
        :else false))

(defn validate-sample
  "Host-admitted sample. :time-ms/:beat/:meter are authoritative; optional
  :device-time-ms is monotonic physical sampling time used only for filtering."
  [sample]
  (when-not (and (map? sample) (= 1 (:version sample 1))
                 (id? (:device-id sample)) (id? (:session-id sample))
                 (integer? (:sample-id sample)) (<= 0 (:sample-id sample) 9007199254740991)
                 (nonnegative? (:time-ms sample)) (finite? (:beat sample))
                 (or (not (contains? sample :device-time-ms)) (nonnegative? (:device-time-ms sample)))
                 (map? (:values sample)) (<= (count (:values sample)) 64)
                 (every? (fn [[k v]] (and (keyword? k) (finite? v))) (:values sample))
                 (vector? (:gestures sample [])) (<= (count (:gestures sample [])) 16))
    (fail! "Sensor sample requires identity, sequence, explicit clocks and finite scalar values"))
  (time/normalize-meter (:meter sample))
  (doseq [gesture (:gestures sample)]
    (when-not (and (map? gesture) (id? (:id gesture)) (keyword? (:type gesture))
                   (= :pulse (:phase gesture))
                   (or (not (contains? gesture :confidence)) (unit? (:confidence gesture))))
      (fail! "Gesture must be an identified semantic pulse, with optional [0,1] confidence")))
  sample)

(defn validate-command
  "Validate portable semantic intent, never an authority envelope. Full fixture/
  registry/parameter admission remains the shared model reducer's responsibility."
  ([command] (validate-command command false))
  ([command template?]
   (when-not (and (map? command) (portable? command)
                  (not-any? #(contains? command %) [:command-id :source :epoch :show-id :time-ms :expected-revision]))
     (fail! "Sensor intents cannot contain transport authority or runtime values"))
   (case (:op command)
     :cue/launch
     (let [launch (:launch command {}) mode (:mode launch :persistent)]
       (when-not (and (id? (:cue-id command)) (map? launch)
                      (#{:persistent :held :timed :one-shot} mode)
                      (map? (:params launch {})))
         (fail! "Invalid cue launch intent"))
       (when (#{:timed :one-shot} mode)
         (when-not (and (empty? (time/validate-duration (:duration launch)))
                        (pos? (val (first (:duration launch)))))
           (fail! "Sensor one-shots/timed launches need an explicit positive duration"))))
     :param/set (when-not (and (id? (:instance-id command)) (keyword? (:param command))
                               (or template? (contains? command :value)))
                  (fail! "Parameter intent needs exact instance, parameter and value"))
     (:instance/end :instance/remove :instance/pause :instance/resume :instance/opacity-toggle)
     (when-not (and (id? (:instance-id command))
                    (or (not (contains? command :force?)) (boolean? (:force? command))))
       (fail! "Instance intent needs exact owned ID"))
     (:instance/opacity-set :master/set)
     (when-not (and (or (= :master/set (:op command)) (id? (:instance-id command)))
                    (or template? (unit? (:value command))))
       (fail! "Intensity/opacity intent needs [0,1] value"))
     :blackout/set (when-not (boolean? (:value command)) (fail! "Blackout intent needs boolean value"))
     (fail! "Unsupported sensor command" {:op (:op command)}))
   command))

(defn validate-commands [commands]
  (when-not (and (vector? commands) (<= (count commands) 256)) (fail! "Commands must be a bounded vector"))
  (doseq [command commands] (validate-command command))
  commands)

(defn transform
  "Apply one stateless scalar transformation. Compose by passing an ordered
  vector to a channel's :transforms. Input/output are finite, never implicit RNG."
  [value spec]
  (when-not (and (finite? value) (map? spec)) (fail! "Transform needs a finite scalar and map"))
  (let [result
        (case (:op spec)
          :offset (do (when-not (finite? (:value spec)) (fail! "Offset must be finite")) (+ value (:value spec)))
          :scale (do (when-not (finite? (:value spec)) (fail! "Scale must be finite")) (* value (:value spec)))
          :abs (Math/abs (double value))
          :negate (- value)
          :clamp (bindings/clamp value (:range spec))
          :map-range (bindings/scale value (:in spec) (:out spec) (:clamp? spec true))
          :deadband (let [width (:width spec)]
                      (when-not (nonnegative? width) (fail! "Deadband width must be nonnegative"))
                      (* (if (neg? value) -1 1) (max 0 (- (Math/abs (double value)) width))))
          :wrap (let [period (:period spec)]
                  (when-not (and (finite? period) (pos? period)) (fail! "Wrap period must be positive"))
                  (- (mod (+ value (/ period 2)) period) (/ period 2)))
          :curve (let [x (bindings/clamp value [0 1])]
                   (case (:kind spec)
                     :linear x :smoothstep (* x x (- 3 (* 2 x)))
                     :ease-in (* x x) :ease-out (- 1 (* (- 1 x) (- 1 x)))
                     (fail! "Unknown scalar curve")))
          (fail! "Unknown sensor transform" {:op (:op spec)}))]
    (when-not (finite? result) (fail! "Sensor transform overflowed")) result))

(defn- input-value [values input]
  (cond
    (keyword? input) (get values input)
    (and (map? input) (= :magnitude (:op input)) (vector? (:inputs input))
         (<= 1 (count (:inputs input)) 8) (every? keyword? (:inputs input)))
    (let [xs (mapv values (:inputs input))]
      (when (every? some? xs) (Math/sqrt (double (reduce + (map #(* % %) xs))))))
    :else (fail! "Channel input is a scalar key or magnitude of explicit scalar keys")))

(defn validate-config [config]
  (when-not (and (map? config) (= 1 (:version config)) (portable? config)
                 (every? #{:version :channels :bindings :triggers :gestures :timeout-ms} (keys config))
                 (and (finite? (:timeout-ms config 500)) (pos? (:timeout-ms config 500))))
    (fail! "Invalid sensor configuration"))
  (doseq [[key limit] [[:channels 32] [:bindings 64] [:triggers 32] [:gestures 16]]]
    (let [xs (get config key [])]
      (when-not (and (vector? xs) (<= (count xs) limit) (every? #(id? (:id %)) xs)
                     (= (count xs) (count (set (map :id xs)))))
        (fail! "Sensor definitions need bounded distinct IDs" {:field key}))))
  (doseq [channel (:channels config)]
    (input-value {} (:input channel))
    (when-not (and (boolean? (:calibrated? channel false))
                   (nonnegative? (:smoothing-ms channel 0))
                   (vector? (:transforms channel [])) (<= (count (:transforms channel [])) 16))
      (fail! "Invalid channel conditioning"))
    (doseq [spec (:transforms channel)] (transform 0.0 spec)))
  (let [channels (set (map :id (:channels config)))]
    (doseq [binding (:bindings config)]
      (when-not (and (or (channels (:channel binding))
                         (and (vector? (:channels binding)) (seq (:channels binding))
                              (every? channels (:channels binding))))
                     (nonnegative? (:epsilon binding 0.001)))
        (fail! "Binding needs known channels and nonnegative epsilon"))
      (when-not (#{:param/set :master/set :instance/opacity-set} (get-in binding [:command :op]))
        (fail! "Continuous bindings target a parameter, master or instance opacity"))
      (when (and (= :param/set (get-in binding [:command :op])) (not (params/valid-schema? (:schema binding))))
        (fail! "Parameter binding requires its complete captured schema"))
      (validate-command (:command binding) true))
    (doseq [trigger (:triggers config)]
      (when-not (and (channels (:channel trigger))
                     (every? finite? [(:on trigger) (:off trigger)])
                     (#{:above :below} (:direction trigger :above))
                     (if (= :below (:direction trigger)) (< (:on trigger) (:off trigger)) (> (:on trigger) (:off trigger))))
        (fail! "Trigger thresholds need a genuine hysteresis interval")))
    (doseq [entry (concat (:triggers config) (:gestures config))]
      (when (seq (time/validate-duration (:cooldown entry {:beats 0}))) (fail! "Invalid musical cooldown"))
      (validate-command (:command entry)))
    (doseq [gesture (:gestures config)]
      (when-not (and (keyword? (:type gesture)) (not= :held (get-in gesture [:command :launch :mode]))
                     (unit? (:min-confidence gesture 0)))
        (fail! "Gesture mappings need semantic pulse type; held mappings use threshold begin/end"))))
  config)

(defn new-state [{:keys [device-id session-id meter armed?] :or {armed? false}}]
  (when-not (and (id? device-id) (id? session-id) (boolean? armed?)) (fail! "Sensor state needs identity and explicit arming"))
  {:version 1 :device-id device-id :session-id session-id :meter (time/normalize-meter meter)
   :armed? armed? :baseline {} :channels {} :triggers {} :bindings {} :holds {:gestures {}}
   :seen-gestures [] :next-gesture 0})

(defn validate-state [state]
  (letfn [(portable-state? [value depth]
            (and (< depth 64) (not (record? value))
                 (or (nil? value) (string? value) (keyword? value) (boolean? value)
                     (and (number? value) (finite? value))
                     (and (vector? value) (every? #(portable-state? % (inc depth)) value))
                     (and (map? value) (every? (fn [[k v]] (and (portable-state? k (inc depth))
                                                                               (portable-state? v (inc depth)))) value)))))]
    (when-not (portable-state? state 0) (fail! "Sensor state must contain only portable immutable data")))
  (when-not (and (map? state) (= 1 (:version state)) (id? (:device-id state)) (id? (:session-id state))
                 (boolean? (:armed? state)) (integer? (:next-gesture state)) (<= 0 (:next-gesture state))
                 (map? (:channels state)) (map? (:baseline state)) (map? (:bindings state))
                 (map? (:triggers state)) (map? (get-in state [:holds :gestures]))
                 (<= (count (get-in state [:holds :gestures])) 128)
                 (vector? (:seen-gestures state)) (<= (count (:seen-gestures state)) 128)
                 (every? id? (:seen-gestures state)))
    (fail! "Invalid owned sensor state"))
  (time/normalize-meter (:meter state))
  (doseq [values [(:baseline state) (:channels state)]]
    (when-not (and (<= (count values) 64) (every? (fn [[k v]] (and (keyword? k) (finite? v))) values))
      (fail! "Invalid sensor calibration/filter values")))
  (doseq [key [:last-time-ms :last-device-time-ms] :when (contains? state key)]
    (when-not (nonnegative? (get state key)) (fail! "Invalid saved sensor timestamp")))
  (when (and (contains? state :last-beat) (not (finite? (:last-beat state)))) (fail! "Invalid saved sensor beat"))
  (when (and (contains? state :last-sample-id)
             (not (and (integer? (:last-sample-id state)) (<= 0 (:last-sample-id state) 9007199254740991))))
    (fail! "Invalid saved sensor sequence"))
  (when-not (every? (fn [[id value]] (and (id? id) (portable? value))) (:bindings state))
    (fail! "Invalid last emitted sensor bindings"))
  (doseq [[_ entry] (:triggers state)]
    (when-not (and (map? entry) (or (not (contains? entry :active?)) (boolean? (:active? entry))))
      (fail! "Invalid sensor hysteresis state"))
    (when-let [timer (:cooldown-timer entry)]
      (when-not (and (map? timer) (#{:ms :beats} (get-in timer [:duration :unit]))
                     (nonnegative? (get-in timer [:duration :value])) (finite? (:started-at timer)))
        (fail! "Invalid sensor cooldown timer"))))
  (doseq [[id hold] (get-in state [:holds :gestures])]
    (when-not (and (string? id) (map? hold) (boolean? (:pressed? hold))
                   (or (not (contains? hold :instance-id)) (id? (:instance-id hold)))
                   (or (not (contains? hold :release-envelope)) (= {} (:release-envelope hold))))
      (fail! "Invalid held sensor ownership")))
  state)

(defn rebase-clock [state beat-delta]
  (validate-state state)
  (when-not (finite? beat-delta) (fail! "Beat rebase delta must be finite"))
  (cond-> (update state :triggers
                  (fn [triggers]
                    (into {} (map (fn [[id entry]]
                                    [id (cond-> entry
                                          (= :beats (get-in entry [:cooldown-timer :duration :unit]))
                                          (update-in [:cooldown-timer :started-at] + beat-delta))])) triggers)))
    (contains? state :last-beat) (update :last-beat + beat-delta)))

(defn calibrate [state sample]
  (validate-sample sample)
  (when (or (:armed? state) (not= (select-keys state [:device-id :session-id]) (select-keys sample [:device-id :session-id])))
    (fail! "Calibrate a disarmed matching session"))
  (assoc state :baseline (:values sample) :channels {} :triggers {} :bindings {}))

(defn- result [state commands events values]
  {:state state :commands (validate-commands (vec commands)) :events (vec events)
   :context {:sensor-values values :sensor-source (select-keys state [:device-id :session-id])}})

(defn- release-holds [state]
  (reduce (fn [{:keys [state commands]} gesture-id]
            (let [released (bindings/end-hold (:holds state) gesture-id {})]
              {:state (assoc state :holds (:state released)) :commands (into commands (:commands released))}))
          {:state state :commands []} (keys (get-in state [:holds :gestures]))))

(defn set-armed [state armed?]
  (when-not (boolean? armed?) (fail! "Armed must be boolean"))
  (let [{:keys [state commands]} (if armed? {:state state :commands []} (release-holds state))]
    (result (assoc state :armed? armed? :triggers {} :bindings {}) commands
            [{:type :sensor/armed :armed? armed?}] {})))

(defn acknowledge
  "Fold an actual shared launch receipt into held ownership; an early release
  emits exactly one end for that instance. Never infer ownership from cue ID."
  [state gesture-id ack]
  (let [next (bindings/acknowledge-hold (:holds state) gesture-id ack)]
    (result (assoc state :holds (:state next)) (:commands next) [] {})))

(defn expire [state config clock]
  (validate-config config)
  (if (and (:armed? state) (:last-time-ms state) (> (- (:time-ms clock) (:last-time-ms state)) (:timeout-ms config 500)))
    (let [released (set-armed state false)]
      (update released :events conj {:type :sensor/dropout :device-id (:device-id state)}))
    (result state [] [] {})))

(defn- conditioned [state config sample]
  (let [physical (:device-time-ms sample (:time-ms sample))
        dt (max 0 (- physical (:last-device-time-ms state physical)))]
    (reduce
     (fn [{:keys [state values]} channel]
       (let [input (:input channel)
             raw-values (if (:calibrated? channel)
                          (reduce-kv (fn [m k v] (assoc m k (- v (get-in state [:baseline k] 0)))) {} (:values sample))
                          (:values sample))
             raw (input-value raw-values input)]
         (if (nil? raw) {:state (update state :channels dissoc (:id channel)) :values values}
             (let [transformed (reduce transform raw (:transforms channel []))
                   previous (get-in state [:channels (:id channel)])
                   tau (:smoothing-ms channel 0)
                   alpha (if (zero? tau) 1.0 (- 1.0 (Math/exp (- (/ (double dt) tau)))))
                   value (if (nil? previous) transformed (+ previous (* alpha (- transformed previous))))]
               (when-not (finite? value) (fail! "Conditioned channel overflowed"))
               {:state (assoc-in state [:channels (:id channel)] value)
                :values (assoc values (:id channel) value)}))))
     {:state state :values {}} (:channels config))))

(defn- cooldown-ready? [entry state clock]
  (or (nil? (:cooldown-timer state)) (:done? (time/sample (:cooldown-timer state) clock))))

(defn- fire [state entry clock]
  (let [command (:command entry)
        held? (= :held (get-in command [:launch :mode]))]
    (if held?
      (do (when (>= (count (get-in state [:holds :gestures])) 128) (fail! "Too many pending held gestures"))
          (let [n (inc (:next-gesture state)) id (str (:device-id state) "/" (:session-id state) "/" n)
                begun (bindings/begin-hold (:holds state) (:cue-id command) {:gesture-id id})]
            {:state (assoc state :next-gesture n :holds (:state begun)) :gesture-id id
             :commands [(merge (first (:commands begun)) command {:gesture-id id})]}))
      {:state state :commands [command]})))

(defn- threshold-step [{:keys [state commands events] :as acc} values clock entry]
  (let [id (:id entry), old (get-in state [:triggers id] {}), value (get values (:channel entry))
        active? (if (nil? value) false
                    (if (= :below (:direction entry))
                      (if (:active? old) (< value (:off entry)) (<= value (:on entry)))
                      (if (:active? old) (> value (:off entry)) (>= value (:on entry)))))
        rising? (and active? (not (:active? old)))
        falling? (and (not active?) (:active? old))
        allowed? (and (:armed? state) rising? (cooldown-ready? entry old clock))
        fired (if allowed? (fire state entry clock) {:state state :commands []})
        released (if (and falling? (:gesture-id old))
                   (let [r (bindings/end-hold (:holds (:state fired)) (:gesture-id old) {})]
                     {:state (assoc (:state fired) :holds (:state r)) :commands (:commands r)})
                   {:state (:state fired) :commands []})
        next (cond-> (assoc old :active? active?)
               allowed? (assoc :cooldown-timer (time/start (:cooldown entry {:beats 0}) clock))
               (:gesture-id fired) (assoc :gesture-id (:gesture-id fired))
               falling? (dissoc :gesture-id))]
    {:state (assoc-in (:state released) [:triggers id] next)
     :commands (into (into commands (:commands fired)) (:commands released))
     :events (cond-> events
               (or rising? falling?) (conj {:type :sensor/threshold :id id :active? active? :value value :fired? (boolean allowed?)}))}))

(defn- binding-value [entry values]
  (let [raw (if (:channels entry) (mapv values (:channels entry)) (get values (:channel entry)))
        schema (:schema entry)]
    (when (if (vector? raw) (every? some? raw) (some? raw))
      (case (:type schema)
        :integer (Math/round (double raw))
        :boolean (>= raw 0.5)
        :enum (let [choices (or (:values schema) (:options schema))
                    x (bindings/clamp raw [0 1])]
                (nth choices (min (dec (count choices)) (long (* x (count choices))))))
        raw))))

(defn- binding-step [{:keys [state commands] :as acc} values entry]
  (let [value (binding-value entry values)
        previous (get-in state [:bindings (:id entry)] ::missing)
        changed? (and (some? value)
                      (if (and (number? value) (number? previous))
                        (> (Math/abs (double (- value previous))) (:epsilon entry 0.001)) (not= value previous)))]
    (when (and (some? value) (:schema entry) (not (params/valid-value? (:schema entry) value)))
      (fail! "Conditioned parameter value violates captured schema" {:binding-id (:id entry)}))
    (if (and (:armed? state) changed?)
      (-> acc (assoc-in [:state :bindings (:id entry)] value)
          (update :commands conj (validate-command (assoc (:command entry) :value value)))) acc)))

(defn step [state config sample]
  (validate-state state)
  (validate-config config) (validate-sample sample)
  (let [physical (:device-time-ms sample (:time-ms sample))
        mismatch (cond
                   (not= (select-keys state [:device-id :session-id]) (select-keys sample [:device-id :session-id])) :wrong-source
                   (<= (:sample-id sample) (:last-sample-id state -1)) :stale-sample
                   (< (:time-ms sample) (:last-time-ms state 0)) :stale-time
                   (< physical (:last-device-time-ms state 0)) :stale-device-time
                   (< (:beat sample) (:last-beat state (:beat sample))) :stale-beat)]
    (if mismatch (result state [] [{:type :sensor/sample-rejected :reason mismatch}] (:channels state))
        (let [clock (assoc (time/frame-clock sample) :meter (:meter state))
              conditioned (conditioned state config sample)
              values (:values conditioned)
              start {:state (:state conditioned) :commands [] :events []}
              thresholds (reduce #(threshold-step %1 values clock %2) start (:triggers config))
              mapped (reduce #(binding-step %1 values %2) thresholds (:bindings config))
              gestures
              (reduce
               (fn [acc gesture]
                 (if (some #{(:id gesture)} (get-in acc [:state :seen-gestures])) acc
                     (let [acc (update-in acc [:state :seen-gestures] #(vec (take-last 128 (conj % (:id gesture)))))]
                       (reduce
                        (fn [acc entry]
                          (let [key [:gesture (:id entry)] old (get-in acc [:state :triggers key])]
                            (if (and (get-in acc [:state :armed?]) (= (:type gesture) (:type entry))
                                     (>= (:confidence gesture 1.0) (:min-confidence entry 0))
                                     (cooldown-ready? entry old clock))
                              (let [fired (fire (:state acc) entry clock)]
                                (-> acc (assoc :state (:state fired))
                                    (assoc-in [:state :triggers key :cooldown-timer] (time/start (:cooldown entry {:beats 0}) clock))
                                    (update :commands into (:commands fired))
                                    (update :events conj {:type :sensor/gesture :id (:id entry) :gesture-id (:id gesture)}))) acc)))
                        acc (:gestures config))))) mapped (:gestures sample))
              state (assoc (:state gestures) :last-time-ms (:time-ms sample) :last-beat (:beat sample)
                           :last-device-time-ms physical :last-sample-id (:sample-id sample))]
          (result state (:commands gestures) (:events gestures) values)))))

(defn middleware
  "Return a pure full-context transform. Store owned state under :sensor-states
  keyed [device-id session-id], values under :sensor-values, append :events and
  :commands. Other context data is preserved. Missing states start disarmed."
  [config sample]
  (validate-config config) (validate-sample sample)
  (fn [context]
    (when-not (and (map? context) (vector? (:commands context [])) (vector? (:events context []))
                   (map? (:sensor-states context {})) (map? (:sensor-values context {})))
      (fail! "Sensor middleware requires vector events/commands and owned state maps"))
    (validate-commands (:commands context []))
    (let [key [(:device-id sample) (:session-id sample)]
          state (get-in context [:sensor-states key] (new-state sample))
          result (step state config sample)]
      (-> context
          (assoc-in [:sensor-states key] (:state result))
          (assoc-in [:sensor-values key] (get-in result [:context :sensor-values]))
          (update :commands #(vec (concat % (:commands result))))
          (update :events #(vec (concat % (:events result))))))))

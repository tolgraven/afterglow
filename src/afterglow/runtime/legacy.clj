(ns afterglow.runtime.legacy
  "Explicit bridge from pure context effects to the existing Afterglow scheduler.

  Each bridge owns its lifecycle/cache under one lock. The inner step receives
  data only. This does not make the rest of the legacy show snapshot-atomic:
  legacy assignment resolvers still own their existing mutable output/history."
  (:require [afterglow.channels :as channels]
            [afterglow.control.params :as schemas]
            [afterglow.effects :as effects]
            [afterglow.effects.channel :as channel]
            [afterglow.effects.color]
            [afterglow.effects.dimmer :as dimmer]
            [afterglow.effects.params :as params]
            [thi.ng.color.core :as color]))

(def ^:private attributes #{:color :dimmer :pan :tilt :focus :zoom :strobe})
(def ^:private blends #{:replace :max :add})

(defn- fail! [message data]
  (throw (ex-info message (assoc data :type ::invalid-bridge))))

(defn- unit? [x]
  (and (schemas/finite-number? x) (<= 0 x 1)))

(defn- valid-time? [x]
  (and (schemas/finite-number? x) (not (neg? x))))

(defn- snapshot-time [snapshot]
  (let [instant (:instant snapshot)]
    (when-not (valid-time? instant)
      (fail! "Legacy bridge needs an explicit finite snapshot :instant" {}))
    instant))

(defn- rgb [value]
  (vec (take 3 @(color/as-rgba value))))

(defn- hsla [components]
  (color/as-hsla (apply color/rgba components)))

(defn- combine [blend previous current]
  (case blend
    :replace current
    :max (max (or previous 0) current)
    :add (min 1.0 (+ (or previous 0) current))))

(defn- rgb-head? [head]
  (every? (set (map :color (:channels head))) [:red :green :blue]))

(defn- color-assigners [head value blend]
  (when (or (rgb-head? head) (seq (:color-wheel-hue-map head)))
    [(effects/build-head-assigner
      :color head
      (fn [show snapshot target previous]
        (let [previous (when (and previous (not= blend :replace))
                         (rgb (params/resolve-param previous show snapshot target)))
              value (if previous (mapv #(combine blend %1 %2) previous value) value)]
          (hsla value))))]))

(defn- raw-assigners [head channels value blend]
  (mapv (fn [ch]
          (channel/build-channel-assigner
           ch (fn [show snapshot _ previous]
                (let [previous (when (and previous (not= blend :replace))
                                 (/ (params/resolve-param previous show snapshot head) 255.0))]
                  (* 255.0 (combine blend previous value)))))) channels))

(defn- function-assigners [head attribute value blend]
  (when-let [[ch spec] (get-in head [:function-map attribute])]
    ;; A normalized value chooses a fraction of the declared function range.
    ;; Legacy scale-fn instead accepts physical units (e.g. Hz). There is no
    ;; general inverse, and mixing those units with old effects is ambiguous.
    (when (and (:scale-fn spec) (not= :replace blend))
      (fail! "Blending with a physically scaled legacy function requires an explicit unit adapter"
             {:target-id (:id head) :attribute attribute :blend blend}))
    (let [target (assoc-in head [:function-map attribute] [ch (dissoc spec :scale-fn)])]
      [(channel/build-head-function-assigner
        attribute target
        (fn [show snapshot target previous]
          (let [previous (when (and previous (not= blend :replace))
                           (/ (params/resolve-param previous show snapshot target) 100.0))]
            (* 100.0 (combine blend previous value)))))])))

(defn- virtual-dimmer [head value blend]
  (when (rgb-head? head)
    (when-not (= :replace blend)
      (fail! "Virtual legacy dimmers support :replace only; use a native dimmer for :max/:add"
             {:target-id (:id head) :blend blend}))
    [(assoc
      (effects/build-head-assigner
       :color head
       (fn [show snapshot target previous]
         (when previous
           (hsla (mapv #(* value %) (rgb (params/resolve-param previous show snapshot target)))))))
      ::virtual-dimmer? true)]))

(defn- assignment-assigners [targets master-scale assignment]
  (let [{:keys [target-id attribute value] :or {value nil}} assignment
        blend (get assignment :blend :replace)
        head (get targets target-id)]
    (when-not (and (map? assignment) head (attributes attribute) (blends blend)
                   (if (= :color attribute)
                     (and (vector? value) (= 3 (count value)) (every? unit? value))
                     (unit? value)))
      (fail! "Invalid normalized legacy bridge assignment"
             {:target-id target-id :attribute attribute :value value :blend blend}))
    (if (= :color attribute)
      (color-assigners head value blend)
      (let [native (filterv #(= attribute (:type %)) (:channels head))
            value (if (= :dimmer attribute) (* master-scale value) value)]
        (cond
          ;; Native dimmers preserve the legacy grand-master and fine-channel path.
          (and (= :dimmer attribute) (seq native)) (raw-assigners head native value blend)
          (get-in head [:function-map attribute]) (function-assigners head attribute value blend)
          (seq native) (raw-assigners head native value blend)
          (= :dimmer attribute) (virtual-dimmer head value blend)
          ;; As with legacy color/function effects, incapable fixtures are skipped.
          :else [])))))

(defn- translate [config show assignments]
  (let [master-scale (if-let [master (:grand-master show)] (dimmer/master-scale master 1.0) 1.0)]
    (when-not (unit? master-scale) (fail! "Invalid legacy grand-master scale" {}))
    ;; A local virtual dimmer follows local color contributions even when the
    ;; declarative output list puts :dimmer first. Cross-effect priority is still
    ;; owned by the legacy show and obeys its existing virtual-dimmer semantics.
    (->> assignments
         (mapcat (partial assignment-assigners (:targets config) master-scale))
         (sort-by #(if (::virtual-dimmer? %) 1 0))
         vec)))

(defn- frame-data [config snapshot last-instant]
  {:time-ms (:instant snapshot)
   :delta-ms (if last-instant (- (:instant snapshot) last-instant) 0)
   :fixtures (:frame-fixtures config)
   :transport {:bpm (:bpm snapshot) :playing? true}
   :metronome (select-keys snapshot [:start :bpm :bpb :bpp :instant :beat :bar :phrase
                                     :beat-phase :bar-phase :phrase-phase])})

(defn- advance-instance [instance instant]
  (let [instance (if (nil? (:started-at-ms instance)) (assoc instance :started-at-ms instant) instance)]
    (if (and (= :running (:phase instance)) (:duration-ms instance)
             (>= instant (+ (:started-at-ms instance) (:duration-ms instance))))
      (assoc instance :phase :releasing
             :release-at-ms (+ (:started-at-ms instance) (:duration-ms instance)))
      instance)))

(defn- expired? [instance instant]
  (and (= :releasing (:phase instance))
       (>= instant (+ (:release-at-ms instance) (:release-duration-ms instance)))))

(defn- evaluate! [bridge show snapshot]
  (locking (:guard bridge)
    (let [before @(:state bridge)
          instant (snapshot-time snapshot)
          owner (:owner before)
          _ (when (and owner (not= owner (:id show)))
              (fail! "A legacy bridge instance cannot be shared between shows" {}))
          _ (when (and (:last-instant before) (< instant (:last-instant before)))
              (fail! "Legacy bridge snapshots must be nondecreasing" {}))]
      (if (= instant (:last-instant before))
        (:cached before)
        (let [config (:config bridge)
              instance (advance-instance (:instance before) instant)
              context {:frame (frame-data config snapshot (:last-instant before))
                       :effect-id (:id instance) :instance instance :state (:state instance)
                       :assignments [] :intents [] :done? false}
              result (if (or (:done? before) (expired? instance instant))
                       (assoc context :done? true)
                       ((:step config) context))
              _ (when-not (and (map? result) (contains? result :state)
                               (vector? (:assignments result)) (vector? (:intents result))
                               (instance? Boolean (:done? result)))
                  (fail! "Pure step returned an invalid context" {:effect-id (:id instance)}))
              assigners (translate config show (:assignments result))
              cached {:active? (or (not (:done? result)) (boolean (seq assigners)))
                      :assigners assigners :intents (:intents result)}
              after (assoc before :owner (:id show) :last-instant instant :cached cached
                           :instance (assoc instance :state (:state result)) :done? (:done? result))]
          ;; One commit only after both pure evaluation and complete translation.
          ;; No callbacks occur in swap!, and failed frames retain prior state.
          (reset! (:state bridge) after)
          cached)))))

(defn- end! [bridge show snapshot]
  (locking (:guard bridge)
    (let [before @(:state bridge)
          _ (when (and (:owner before) (not= (:owner before) (:id show)))
              (fail! "A legacy bridge instance cannot be shared between shows" {}))
          ;; The legacy render loop may already have evaluated a predicted next
          ;; snapshot when a controller requests release. Never rewind that frame.
          instant (max (snapshot-time snapshot) (or (:last-instant before) 0))
          instance (advance-instance (:instance before) instant)
          immediate? (or (:done? before) (= :releasing (:phase instance))
                         (zero? (:release-duration-ms instance)))
          instance (assoc instance :phase :releasing :release-at-ms instant)]
      (reset! (:state bridge)
              (cond-> (assoc before :owner (:id show) :instance instance :done? immediate?)
                immediate? (assoc :cached {:active? false :assigners [] :intents []})))
      immediate?)))

(defn- initial-instance [config params state started-at-ms]
  {:id (:instance-id config) :effect-id (get-in config [:definition :id])
   :definition (:definition config) :effect-version (get-in config [:definition :version])
   :params params :state state :started-at-ms started-at-ms :phase :running
   :launch-mode (:mode config)
   :duration-ms (:duration-ms config) :release-duration-ms (:release-duration-ms config)})

(defn effect
  "Create a real legacy IEffect from a pure context step and patched fixtures.

  Options: :definition, :step, :fixtures, optional :params, :name, :instance-id,
  :initial-state, :started-at-ms, :mode, :duration-ms and :release-duration-ms.
  Mode defaults to :persistent, or :timed when an explicit :duration-ms is given.
  :timed/:one-shot modes require a positive explicit or definition duration;
  :persistent/:held modes do not expire just because the definition has one.
  Without
  an explicit start instant, the first supplied metronome snapshot starts it.
  There are no constructor clocks or output side effects. Pass the result to
  show/add-effect! or a legacy cue factory. Create a fresh bridge per activation.

  The step sees immutable parameter/state maps, numeric fixture descriptors and
  explicit snapshot time, never the mutable legacy show or Java3D objects.
  still-active? and generate share one evaluation per snapshot instant. State
  updates and assigner translation commit together under this instance's lock.
  A terminal step may contribute one final frame before becoming inactive.

  RGB becomes thi.ng HSLA for this fork's color resolver. Normalized :pan/:tilt
  are fractions of raw fixture function ranges, NOT world-space angles; existing
  world-space movement effects retain their legacy resolution precedence.
  :focus/:zoom/:strobe also select function-range fractions, bypassing physical
  scale-fn units. Such scaled functions support :replace blending only. Fixtures
  lacking an attribute are skipped, as with legacy attribute effects; unknown
  targets/attributes or invalid values fail before state publication.

  Native/virtual dimmers use a captured grand-master scale. Virtual RGB dimming
  supports :replace only and applies after this effect's colors. Named function
  resolution retains legacy range rounding and mutable movement history.
  Returned intents are available via frame-info; this bridge never executes them.
  This is an adapter, not a claim of whole-show snapshot or output atomicity."
  [{:keys [definition step fixtures params name instance-id initial-state started-at-ms
           duration-ms release-duration-ms]
    :or {params {} initial-state {}} :as options}]
  (when-not (and (map? definition) (some? (:id definition))
                 (integer? (:version definition)) (pos? (:version definition))
                 (ifn? step) (sequential? fixtures)
                 (or (nil? started-at-ms) (valid-time? started-at-ms)))
    (fail! "Invalid legacy bridge definition, step, fixtures or start time" {}))
  (let [initial-state (get options :initial-state (get definition :initial-state {}))
        heads (vec (channels/expand-heads fixtures))
        ids (mapv :id heads)
        _ (when-not (and (every? some? ids) (= (count ids) (count (set ids))))
            (fail! "Bridge fixtures/heads must be patched with unique IDs" {}))
        _ (doseq [ch (mapcat :channels heads)]
            (when-not (and (integer? (:universe ch)) (integer? (:address ch)) (integer? (:index ch)))
              (fail! "Bridge channels must be patched before construction" {})))
        params (schemas/resolve-values (:params definition {}) params)
        mode (get options :mode (if (contains? options :duration-ms) :timed :persistent))
        _ (when-not (#{:persistent :held :timed :one-shot} mode)
            (fail! "Unknown bridge launch mode" {:mode mode}))
        duration-ms (when (#{:timed :one-shot} mode) (or duration-ms (:duration-ms definition)))
        release-duration-ms (or release-duration-ms (:release-duration-ms definition)
                                (get-in definition [:envelope :release-ms]) 0)
        _ (when-not (and (if (#{:timed :one-shot} mode)
                           (and (schemas/finite-number? duration-ms) (pos? duration-ms))
                           (nil? duration-ms))
                         (valid-time? release-duration-ms))
            (fail! "Invalid bridge duration or release duration" {}))
        config (assoc options :definition definition :step step :initial-state initial-state
                      :instance-id (or instance-id (str "legacy/" (:id definition)))
                      :mode mode :duration-ms duration-ms :release-duration-ms release-duration-ms
                      :targets (zipmap ids heads)
                      :frame-fixtures (mapv (fn [head]
                                              {:id (:id head) :name (:name head)
                                               :position (mapv #(double (get head % 0)) [:x :y :z])})
                                            (filter #(seq (:channels %)) heads)))
        state (atom {:generation 0 :owner nil :last-instant nil :cached nil :done? false
                     :instance (initial-instance config params initial-state started-at-ms)})
        bridge {:config config :guard (Object.) :state state}]
    ;; show/add-effect! requires the concrete Effect record, not only IEffect.
    (assoc (effects/->Effect (or name (:name definition) (str (:id definition)))
                             (fn [show snapshot] (:active? (evaluate! bridge show snapshot)))
                             (fn [show snapshot] (:assigners (evaluate! bridge show snapshot)))
                             (fn [show snapshot] (end! bridge show snapshot)))
           ::boundary bridge)))

(defn- boundary [effect]
  (or (::boundary effect) (fail! "Expected an effect created by the legacy context bridge" {})))

(defn set-params!
  "Validate and merge parameter updates. An already evaluated snapshot stays
  cached; new values enter the next snapshot. This is an explicit boundary API."
  [effect values]
  (when-not (map? values) (fail! "Parameter updates must be a map" {}))
  (let [bridge (boundary effect)]
   (locking (:guard bridge)
    (let [before @(:state bridge)
          values (schemas/resolve-values (get-in bridge [:config :definition :params] {})
                                         (merge (get-in before [:instance :params]) values))]
      (reset! (:state bridge) (assoc-in before [:instance :params] values))
      values))))

(defn reset-effect!
  "Explicitly begin a fresh generation without creating a shared global state.
  Options may replace :params, :state and :started-at-ms; defaults retain current
  params, restore initial state, and start on the next supplied snapshot. Owner
  show identity remains fixed; construct a new bridge for another show/patch."
  ([effect] (reset-effect! effect {}))
  ([effect options]
   (when-not (map? options) (fail! "Reset options must be a map" {}))
   (let [bridge (boundary effect)]
    (locking (:guard bridge)
     (let [before @(:state bridge)
           config (:config bridge)
           start (:started-at-ms options)
           _ (when-not (or (nil? start) (valid-time? start)) (fail! "Invalid bridge reset time" {}))
           params (schemas/resolve-values (get-in config [:definition :params] {})
                                          (get options :params (get-in before [:instance :params])))
           state (get options :state (:initial-state config))]
       (reset! (:state bridge)
               (assoc before :generation (inc (:generation before)) :last-instant nil
                      :cached nil :done? false :instance (initial-instance config params state start)))
       effect)))))

(defn frame-info
  "Read immutable diagnostics/intent data for the last evaluated frame.
  Consumers deduplicate intents using [generation instant]; no history is queued."
  [effect]
  (let [bridge (boundary effect)
        {:keys [generation last-instant instance cached done?]} @(:state bridge)]
    {:generation generation :instant last-instant :state (:state instance)
     :params (:params instance) :phase (:phase instance) :done? done?
     :active? (:active? cached) :intents (:intents cached)}))

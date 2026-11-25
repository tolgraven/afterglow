(ns afterglow.control.devices.push-cue-gesture
  "Pure Push cue-pad policy. Profiles own decoded note identity, overlay routing,
  and deadline delivery. The show owner admits the returned commands."
  (:require [afterglow.control.bindings :as bindings]
            [afterglow.control.devices.expressive :as expressive]
            [afterglow.control.devices.push-launch :as launch]
            [afterglow.control.pages :as pages]
            [afterglow.control.parameter-edit :as edit]
            [afterglow.control.params :as params]
            [afterglow.control.views :as views]))

(defn configure
  "Compile gesture options. :button-bindings maps captured control IDs to
  actions. :gesture-modifier defaults to :cue-gesture; nil disables it. :axes
  names the per-note expression available to this profile. :legacy-velocity?
  enables Push 2's authored velocity endpoints for strike and pressure."
  [options]
  (let [hold-ms (:hold-ms options 220)
        modifier (:gesture-modifier options :cue-gesture)
        axes (set (:axes options #{:strike :pressure}))]
    (when-not (and (params/finite-number? hold-ms) (pos? hold-ms)
                   (or (nil? modifier) (keyword? modifier))
                   (every? #{:strike :pressure :glide :slide} axes))
      (throw (ex-info "Invalid Push cue gesture options" {})))
    (expressive/normalize-policy (:mapping-policy options {}))
    (expressive/normalize-policy {:params (:param-mappings options {})})
    (doseq [mappings (vals (:cue-mappings options))]
      (expressive/normalize-policy {:params mappings}))
    (assoc options :hold-ms hold-ms :gesture-modifier modifier :axes axes ::grid (launch/grid options))))

(defn initial-state [] {:pads {} :holds {} :next-order 0})

(defn- show-key [data] [(:show-id data) (:epoch data)])

(defn- sync-context [state surface model]
  (let [show (show-key model)
        page [(:page-id surface :main) (:origin surface [0 0])]]
    (cond
      (not= show (:show state)) (assoc (initial-state) :show show :page page)
      (= page (:page state)) state
      :else (-> state (assoc :page page) (dissoc :selection)
                (update :pads update-vals #(assoc % :view-detached? true))))))

(defn- cue-at [model [page origin] cell]
  (when cell
    (get-in model [:registry :cues (pages/cue-id-at model page (mapv + origin cell))])))

(defn- definition [model cue]
  (let [id (:effect-id cue)
        current (get-in model [:registry :effects id])]
    (if-let [version (:effect-version cue)]
      (or (get-in model [:registry :versions [:effects id version]])
          (when (= version (:version current)) current))
      current)))

(defn- expression-plan [options model device-id cue-id schemas]
  (let [policy (expressive/policy model device-id cue-id (expressive/profile-defaults options cue-id))
        overrides (:params policy)
        disabled-axes (into #{} (map keyword) (:disabled-axes policy))
        legacy-axes (when (and (:legacy-velocity? options) (:enabled? policy))
                      (into #{} (filter #(and (contains? (:axes options) %)
                                              (not (contains? disabled-axes %))))
                            [:strike :pressure]))
        legacy-params (when (seq legacy-axes)
                        (into #{} (keep (fn [[param schema]]
                                         (when (and (:velocity schema) (#{:number :integer} (:type schema))
                                                    (not (contains? schema :control/axis))
                                                    (not (contains? overrides param))) param)))
                              schemas))]
    (assoc (expressive/plan (apply dissoc schemas legacy-params) (:axes options) overrides
                            (dissoc policy :params))
           :legacy-axes legacy-axes :legacy-params (select-keys schemas legacy-params))))

(defn- expression-values [plan axes current]
  (let [legacy (when-let [value (some #(when (contains? (:legacy-axes plan) %) (get axes %))
                                    [:pressure :strike])]
                 (edit/velocity-values {:params (:legacy-params plan)} value))]
    (merge legacy (expressive/values plan axes current))))

(defn- edit-commands [options model pad axes]
  (let [instance (get-in model [:instances (:instance-id pad)])]
    (when (= :running (:phase instance))
      (let [current (:params instance)
            plan (expression-plan options model (:device-id pad) (:cue-id pad) (get-in instance [:definition :params]))]
        (into [] (comp (remove (fn [[param value]] (= value (get current param))))
                       (map (fn [[param value]] {:op :param/set :instance-id (:id instance) :param param :value value})))
              (sort-by (comp str key) (expression-values plan axes current)))))))

(defn- launch-cue [options state key pad mode envelope]
  (let [{:keys [cue-id token launch-data pressed-at]} pad
        grid (::grid options)
        launch-context (assoc envelope :gesture-id token)
        held? (= :held mode)
        hold (when held? (bindings/begin-hold (:holds state) cue-id launch-context grid))
        command (if held? (first (:commands hold))
                    (cond-> (assoc envelope :op :cue/launch :cue-id cue-id)
                      grid (assoc :command-id token :grid grid)))
        command (cond-> (assoc command ::key key ::token token :command-id token
                              :launch (assoc launch-data :mode mode))
                  grid (assoc :raw {:time-ms pressed-at}))]
    {:state (cond-> state held? (assoc :holds (:state hold)))
     :commands [command]}))

(defn- modifier-held? [{:keys [gesture-modifier button-bindings]} surface]
  (and gesture-modifier (some #(= gesture-modifier (get button-bindings %)) (:pressed-buttons surface))))

(defn- press [options state {:keys [gesture-key cell value axes]} surface model envelope]
  (if-let [cue (cue-at model (:page state) cell)]
    (let [cue-id (:id cue)
          cue-definition (definition model cue)
          instances (filter #(= cue-id (:cue-id %)) (views/active-instances model))
          active (or (last (filter #(= :running (:phase %)) instances)) (last instances))
          authored-mode (or (:launch-mode options) (:launch-mode cue) (when (:held cue) :held)
                            (:default-launch-mode options) :persistent)
          device-id (or (:mapping-id options) (:session-id options) (get-in envelope [:source :session-id]))
          plan (expression-plan options model device-id cue-id (:params cue-definition {}))
          expressive? (or (seq (:mappings plan)) (seq (:legacy-params plan)))
          modifier? (modifier-held? options surface)
          strike (cond-> (select-keys axes (:axes options)) (some? value) (assoc :strike value))
          target (:target-selector surface)
          kind (cond
                 (and modifier? active) :select
                 (or target (#{:one-shot :timed} authored-mode)) :launch
                 active :active-wait
                 (or modifier? (not expressive?)) :idle-wait
                 :else :launch)
          launch-data (when (#{:launch :idle-wait} kind)
                        (let [current (merge (update-vals (:params cue-definition {}) :default)
                                             (:params cue) (:saved-params cue))]
                          (cond-> {:velocity (:strike strike) :params (expression-values plan strike current)}
                            target (assoc :selector target))))
          token (:command-id envelope)
          pad {:kind kind :token token :cue-id cue-id :cue-version (:version cue)
               :definition-version (:version cue-definition) :cell cell
               :device-id device-id :instance-id (when (#{:select :active-wait} kind) (:id active))
               :force? (= :releasing (:phase active)) :strike (select-keys strike [:strike])
               :order (:next-order state) :pressed-at (:time-ms envelope)
               :deadline (+ (:time-ms envelope) (:hold-ms options)) :launch-data launch-data}
          state (-> state (assoc-in [:pads gesture-key] pad) (update :next-order inc')
                    (assoc :selection (select-keys pad [:token :cue-id :instance-id])))]
      (if (= kind :launch)
        (cond-> (launch-cue options state gesture-key pad authored-mode envelope)
          target (assoc :target-consumed? true))
        {:state state}))
    {:state (assoc-in state [:pads gesture-key] {:kind :empty})}))

(defn- same-cell? [state model pad]
  (when-not (:view-detached? pad)
    (let [cue (cue-at model (:page state) (:cell pad))]
      (and (= (:cue-id pad) (:id cue)) (= (:cue-version pad) (:version cue))
           (or (:instance-id pad) (= (:definition-version pad) (:version (definition model cue))))))))

(defn- exact-active? [model pad]
  (= (:cue-id pad) (get-in model [:instances (:instance-id pad) :cue-id])))

(defn- release [options state key pad model envelope cancelled?]
  (let [state (update state :pads dissoc key)
        hold? (contains? (get-in state [:holds :gestures]) (:token pad))
        short? (and (:deadline pad) (< (:time-ms envelope) (:deadline pad)))]
    (cond
      hold? (let [result (bindings/end-hold (:holds state) (:token pad) envelope)]
              {:state (assoc state :holds (:state result)) :commands (:commands result)})
      (and (not cancelled?) short? (same-cell? state model pad))
      (case (:kind pad)
        :idle-wait (launch-cue options state key pad :persistent envelope)
        :active-wait {:state state :commands (when (exact-active? model pad)
                                               [{:op :instance/end :instance-id (:instance-id pad) :force? (:force? pad)}])}
        {:state state})
      :else {:state state})))

(defn- waiting? [pad]
  (and (#{:idle-wait :active-wait} (:kind pad)) (not (:view-detached? pad))))

(defn next-deadline-ms
  "Earliest undecided pad deadline, or nil. Drive :tick using the same logical
  clock as input. Each due pad is decided at most once."
  [state]
  (when-let [deadlines (seq (map :deadline (filter waiting? (vals (:pads state)))))]
    (reduce min deadlines)))

(defn- tick [options state model envelope]
  (reduce (fn [{:keys [state commands]} [key pad]]
            (let [matches? (same-cell? state model pad)
                  kind (cond
                         (not matches?) :empty
                         (and (= :active-wait (:kind pad)) (exact-active? model pad)) :active-hold
                         (= :idle-wait (:kind pad)) :launch
                         :else :empty)
                  next-state (assoc-in state [:pads key :kind] kind)
                  result (case kind
                           :launch (launch-cue options next-state key pad :held envelope)
                           :active-hold {:state next-state :commands (edit-commands options model pad (:strike pad))}
                           {:state next-state})
                  next-commands (into commands (:commands result))]
              ;; The session admits at most 64 commands per transition. Leave
              ;; remaining pads undecided for the next refresh.
              (if (> (count next-commands) 64)
                (reduced {:state state :commands commands})
                (assoc result :commands next-commands))))
          {:state state :commands []}
          (sort-by (fn [[_ pad]] [(:deadline pad) (:order pad)])
                   (filter (fn [[_ pad]] (and (waiting? pad) (<= (:deadline pad) (:time-ms envelope))))
                           (:pads state)))))

(defn step
  "Apply :pad, :axis, :tick or :context to the gesture state. A :pad event
  carries :gesture-key, :pressed?, :cell, and normalized :value or :axes.
  Set :cancelled? on synthetic releases such as MPE retriggers or all-notes-off.
  :axis carries the same :gesture-key, :axis and normalized :value. The surface
  carries :page-id, :origin, :pressed-buttons, :target-selector, and :pad-owner
  when an overlay claims a new pad. An existing pad retains its release.
  Results may indicate :pass-through? or :target-consumed?."
  [options state {:keys [type gesture-key pressed? axis value] :as event} surface model envelope]
  (let [state (sync-context state surface model)
        pad (get-in state [:pads gesture-key])]
    (if (not= (show-key model) (show-key envelope))
      {:state state}
      (let [result (case type
                     :pad (cond
                            (and pad pressed?) {:state state}
                            pad (release options state gesture-key pad model envelope (:cancelled? event))
                            (or (:pad-owner surface) (not pressed?)) {:state state :pass-through? true}
                            :else (press options state event surface model envelope))
                     :axis {:state state :commands (when (and (#{:active-hold :launch} (:kind pad))
                                                             (same-cell? state model pad)
                                                             (params/finite-number? value)
                                                             (contains? (:axes options) axis))
                                                    (edit-commands options model pad {axis value}))}
                     :tick (tick options state model envelope)
                     {:state state})]
        (cond-> result
          (seq (:commands result)) (update :commands #(mapv (fn [command] (merge (select-keys envelope [:show-id :epoch]) command)) %)))))))

(defn acknowledge
  "Apply this policy's launch receipt. Quantized receives can supply :pending
  and later :fired/:missed/:cancelled for the same command, or use push-launch's
  terminal status normalization. Receipts cannot reacquire a pad or selection."
  [state {:keys [command-id] :as command} ack]
  (let [token (::token command) key (::key command)
        pad (get-in state [:pads key])
        accepted? (and (#{:accepted :fired} (:status ack)) (:instance-id ack))]
    (if (and token (= :cue/launch (:op command)) (= (:show state) (show-key command))
             (every? #(or (not (contains? ack %)) (= (get command %) (get ack %))) [:show-id :epoch :command-id])
             (#{:accepted :fired :rejected :missed :cancelled} (:status ack)))
      (let [hold (when (= :held (get-in command [:launch :mode]))
                   (bindings/acknowledge-hold (:holds state) token (assoc ack :status (if accepted? :accepted :rejected))))]
        {:state (cond-> state
                  hold (assoc :holds (:state hold))
                  (and accepted? (= token (:token (:selection state))))
                  (assoc-in [:selection :instance-id] (:instance-id ack))
                  (and accepted? (not (:view-detached? pad)) (= token (:token pad)))
                  (assoc-in [:pads key :instance-id] (:instance-id ack)))
         :commands (:commands hold)})
      {:state state})))

(defn stop
  "Drop local input state and emit release/cancel commands for owned launches."
  [state envelope]
  {:state (initial-state)
   :commands (when (= (:show state) (show-key envelope)) (bindings/release-holds (:holds state) envelope))})

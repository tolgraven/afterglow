(ns afterglow.control.effect-selection
  "Pure Solo and Mute policy for running show instances."
  (:require [clojure.set :as set]
            [afterglow.control.categories :as categories]
            [afterglow.control.instance-order :as instance-order]))

(def ^:private default-modes {:solo :exclusive :mute :exclusive})

(defn- reject! [code message & [details]]
  (throw (ex-info message {:control/error code :details details})))

(defn- mode-entry? [[control mode]]
  (and (contains? default-modes control) (#{:exclusive :additive} mode)))

(defn- modes [model]
  (let [configured (get-in model [:settings :effect-selection])]
    (into default-modes (filter mode-entry?) (when (map? configured) configured))))

(defn- layer-id [instance]
  (get-in instance [:source :native-layer :id]))

(defn- selected? [instance control]
  (contains? (::selected instance) control))

(defn- solo-active? [instances]
  (boolean (some #(selected? % :solo) instances)))

(defn- suppression [solo-active? soloed? muted?]
  (cond muted? :mute (and solo-active? (not soloed?)) :solo))

(defn suppressed-instance-ids
  "IDs whose output is gated among the instances participating in this frame."
  [instances]
  (if (some ::selected instances)
    (let [solo? (solo-active? instances)]
      (into #{} (keep (fn [instance]
                        (when (suppression solo? (selected? instance :solo) (selected? instance :mute))
                          (:id instance)))) instances))
    #{}))

(defn- select-targets [model selector instances]
  (let [layer? (and (map? selector) (contains? selector :layer-id))
        layer (:layer-id selector)
        matches (categories/select-instances model (if layer? (dissoc selector :layer-id) selector))]
    (when layer?
      (when-not (or (keyword? layer) (and (string? layer) (seq layer)))
        (reject! :invalid-selector "A native layer selector needs a stable layer ID"))
      (when-not (some #(= layer (layer-id %)) instances)
        (reject! :unknown-layer "The native layer has no active instances" {:layer-id layer})))
    (into #{} (comp (filter #(or (not layer?) (= layer (layer-id %)))) (map :id)) matches)))

(defn- select-ids [current targets mode]
  (cond
    (empty? targets) current
    (= :exclusive mode) (if (= current targets) #{} targets)
    (set/subset? targets current) (set/difference current targets)
    :else (set/union current targets)))

(defn- mark [instance control selected]
  (let [flags (or (::selected instance) #{})
        flags (if (contains? selected (:id instance)) (conj flags control) (disj flags control))]
    (if (seq flags) (assoc instance ::selected flags) (dissoc instance ::selected))))

(defn- action-mode
  "The mode for one toggle: an explicit :mode, the :additive? shorthand, or
  the configured mode for the control."
  [model {:keys [control additive? mode] :as command}]
  (when (and (contains? command :additive?) (not (boolean? additive?)))
    (reject! :invalid-value "The additive modifier must be boolean"))
  (when (and (contains? command :mode) (not (#{:exclusive :additive} mode)))
    (reject! :invalid-value "A toggle mode is :exclusive or :additive" {:mode mode}))
  (when (and (some? mode) (contains? command :additive?) (not= additive? (= :additive mode)))
    (reject! :invalid-value "The additive modifier contradicts the toggle mode"
             {:mode mode :additive? additive?}))
  (cond mode mode additive? :additive :else (get (modes model) control)))

(defn- toggle [model {:keys [control selector] :as command}]
  (when-not (contains? default-modes control)
    (reject! :invalid-control "Effect selection controls are Solo and Mute"))
  (let [mode (action-mode model command)
        instances (instance-order/ordered model)
        targets (select-targets model selector instances)
        current (into #{} (comp (filter #(selected? % control)) (map :id)) instances)
        selected (select-ids current targets mode)
        ordered (mapv :id instances)
        changed (filterv #(not= (contains? current %) (contains? selected %)) ordered)
        result {:control control :mode mode :instance-ids (filterv targets ordered)
                :selected-instance-ids (filterv selected ordered)
                :changed-instance-ids changed}]
    {:model (reduce (fn [m id] (update-in m [:instances id] mark control selected)) model changed)
     :result result
     :events (if (seq changed) [(assoc result :type :effect-selection/changed)] [])}))

(defn- configure [model patch]
  (when-not (and (map? patch) (seq patch) (every? mode-entry? patch))
    (reject! :invalid-value "Set an exclusive or additive mode for Solo or Mute"))
  (let [configured (merge (modes model) patch)
        result {:modes configured}]
    (if (= (modes model) configured)
      {:model model :result result :events []}
      {:model (assoc-in model [:settings :effect-selection] configured)
       :result result
       :events [(assoc result :type :effect-selection/configured)]})))

(defn apply-operation
  "Apply a selection operation within the shared command reducer. Selectors use
  the category selector dimensions and optionally a native :layer-id. A toggle's
  :mode (:exclusive or :additive) overrides the configured mode for that action
  only; :additive? true is shorthand for :mode :additive, and a command giving
  both must agree. Invalid operations throw a :control/error."
  [model {:keys [op modes] :as command}]
  (case op
    :effect-selection/toggle (toggle model command)
    :effect-selection/configure (configure model modes)
    (reject! :unknown-operation "Unknown effect selection operation")))

(defn- group-state [instances field]
  (let [n (count (filter field instances))]
    (cond
      (zero? n) :none
      (= n (count instances)) :all
      :else :partial)))

(defn projection
  "Describe selected and suppressed instances in render input order. A selected
  Mute always suppresses its instance. Any active Solo selection suppresses
  every other instance, including when each soloed instance is also muted. A
  caller can pass the already ordered instances from the same model."
  ([model] (projection model (instance-order/ordered model)))
  ([model instances]
   (let [solo? (solo-active? instances)
         rows (mapv (fn [instance]
                      (let [soloed? (selected? instance :solo)
                            muted? (selected? instance :mute)
                            layer (layer-id instance)]
                        (cond-> {:id (:id instance) :soloed? soloed? :muted? muted?
                                 :suppressed-by (suppression solo? soloed? muted?)}
                          layer (assoc :layer-id layer))))
                    instances)
         layers (group-by :layer-id rows)
         layer-ids (into [] (comp (keep :layer-id) (distinct)) rows)]
     {:modes (modes model)
      :solo-active? solo?
      :included-instance-ids (into [] (comp (remove :suppressed-by) (map :id)) rows)
      :instances rows
      :layers (mapv (fn [id]
                      (let [members (get layers id)]
                        {:id id :instance-ids (mapv :id members)
                         :solo (group-state members :soloed?) :mute (group-state members :muted?)}))
                    layer-ids)})))

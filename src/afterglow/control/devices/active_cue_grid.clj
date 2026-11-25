(ns afterglow.control.devices.active-cue-grid
  "Pure active pad modes. The adapter publishes a projection, then captures the
  mapping that is visible on that surface before admitting its pad presses."
  (:require [afterglow.control.instance-order :as instance-order]
            [afterglow.control.views :as views]))

(def initial-state {:mode nil :page 0 :layout 0 :pressed #{}})

(def ^:private page-size 64)

(defn- running [model]
  (filterv #(= :running (:phase %)) (instance-order/ordered model)))

(defn- page-count [instances]
  (max 1 (quot (+ (count instances) (dec page-size)) page-size)))

(defn set-mode
  "Switch between :select, :reorder and nil. Outstanding physical presses
  remain owned by this grid until release, even after it closes."
  [state mode]
  (when-not (contains? #{nil :select :reorder} mode)
    (throw (ex-info "Unknown active cue grid mode" {:mode mode})))
  (if (= mode (:mode state)) state
      (-> state (assoc :mode mode :page 0) (update :layout inc) (dissoc :capture :source))))

(defn step-page [state model delta]
  (if (:mode state)
    (let [last-page (dec (page-count (running model)))
          from (min (:page state) last-page)
          page (max 0 (min (+ from delta) last-page))]
      (if (= page (:page state)) state
          (-> state (assoc :page page) (update :layout inc) (dissoc :capture))))
    state))

(defn- stamp [model]
  (select-keys model [:show-id :epoch :revision]))

(defn- order-identity [stamp ids]
  [(:show-id stamp) (:epoch stamp) ids])

(defn- pad [model source index {:keys [id cue-id effect-id effect-version params definition] :as instance}]
  (let [cue (views/pad-view model cue-id {cue-id [instance]})]
    {:x (mod index 8) :y (quot index 8) :instance-id id :cue-id cue-id
     :effect-id effect-id :effect-version effect-version
     :name (or (:name cue) (:name definition) (str (or cue-id effect-id)))
     :color (or (:color cue) (:color params) (:color definition)
                (views/swatch-rgb (:swatch definition)) [0.35 0.35 0.35])
     :source? (= id source)}))

(defn project
  "Build a zero-based page in render input order. Coordinates start at the
  lower-left pad and fill each row left to right. :view is for feedback and
  :capture provides the exact mapping to record when that feedback is visible."
  [state model]
  (when-let [mode (:mode state)]
    (let [instances (running model)
          pages (page-count instances)
          page (min (:page state) (dec pages))
          offset (* page-size page)
          visible (subvec instances offset (min (count instances) (+ offset page-size)))
          stamp (stamp model)
          ids (mapv :id instances)
          order (order-identity stamp ids)
          source (when (= order (get-in state [:source :order])) (get-in state [:source :instance-id]))]
      {:view {:mode mode :page page :page-count pages :instance-count (count instances)
              :source-instance-id source
              :cells (mapv (partial pad model source) (range (count visible)) visible)}
       :capture {:layout (:layout state) :page page :stamp stamp :order order
                 :selections (mapv (fn [{:keys [id cue-id]}] {:instance-id id :cue-id cue-id}) visible)}})))

(defn capture
  "Record the exact projected pad mapping after the adapter publishes it. A
  late feedback completion from a different mode or page is ignored."
  [state projection]
  (let [{:keys [layout order page] :as visible} (:capture projection)]
    (if (and (:mode state) (= (:layout state) layout))
      (cond-> (assoc state :capture visible :page page)
        (not= order (get-in state [:source :order])) (dissoc :source))
      state)))

(defn- pad-index [coordinate]
  (when (and (vector? coordinate) (= 2 (count coordinate))
             (every? #(and (integer? %) (<= 0 % 7)) coordinate))
    (let [[x y] coordinate] (+ x (* 8 y)))))

(defn press
  "Handle a physical down event. The pad key must also reach release, even when
  the overlay is closed. An unmatched or stale view consumes the press without
  redirecting it. Other pad owners retain release routing for their own holds."
  [state model pad-key coordinate]
  (cond
    (contains? (:pressed state) pad-key) {:state state :handled? true :commands []}
    (nil? (:mode state)) {:state state :handled? false :commands []}
    :else
    (let [state (update state :pressed conj pad-key)
          {:keys [order selections] captured-stamp :stamp} (:capture state)
          result {:state state :handled? true :commands []}
          current-stamp (stamp model)]
      (if-let [{:keys [instance-id] :as selection}
               (when (and (= captured-stamp current-stamp)
                          (= order (order-identity current-stamp (mapv :id (running model)))))
                 (when-let [index (pad-index coordinate)] (get selections index)))]
        (if (= :select (:mode state))
          (assoc result :selection selection)
          (let [source (get-in state [:source :instance-id])]
            (cond
              (nil? source) (assoc-in result [:state :source] {:instance-id instance-id :order order})
              (= source instance-id) (update result :state dissoc :source)
              :else (assoc result :state (dissoc state :source :capture)
                                  :commands [(assoc (dissoc current-stamp :revision) :op :instance/move-after
                                                    :instance-id source :after-instance-id instance-id
                                                    :expected-revision (:revision current-stamp))]))))
        result))))

(defn release [state pad-key]
  {:state (update state :pressed disj pad-key)
   :handled? (contains? (:pressed state) pad-key)
   :commands []})

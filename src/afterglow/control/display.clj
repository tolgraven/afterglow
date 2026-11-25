(ns afterglow.control.display
  "Presentation choices owned by a control session. A display gesture never
  changes the show or launches a cue."
  (:require [afterglow.control.pages :as pages]))

(def modes #{:parameters :pages :simulator :rig :audio :block-trace})

(def page-palettes [:both :cue :type])

(def parameter-views [:auto :history :spatial :controls])

(def history-spans [0.5 1 2 4 8 16])

(def camera-lenses [:fit :panorama :audience])

(def parameter-only-capabilities {:modes #{:parameters} :actions #{}})

(defn option [state model k default]
  (get state k (get-in model [:settings :controllers :push-display k] default)))

(defn mode [state model]
  (let [supported (get-in state [:display-capabilities :modes])
        preferred [(:display-mode state) (get-in model [:settings :controllers :push-display :mode]) :parameters]]
    (if supported
      (or (some supported preferred) (first (sort supported)))
      (some identity preferred))))

(defn page-ids [model]
  (pages/page-ids model))

(defn page-window [ids page bank]
  (let [banks (max 1 (quot (+ (count ids) 7) 8))
        current (quot (max 0 (.indexOf ^java.util.List ids page)) 8)
        bank (min (dec banks) (max 0 (if (nat-int? bank) bank current)))
        start (* 8 bank)]
    {:bank bank :banks banks :pages (subvec ids start (min (+ start 8) (count ids)))}))

(defn- step-choice [choices current step wrap?]
  (let [i (+ step (max 0 (.indexOf ^java.util.List choices current)))]
    (nth choices (if wrap? (mod i (count choices)) (min (dec (count choices)) (max 0 i))))))

(defn- next-option [state model k choices default step wrap?]
  (assoc state k (step-choice choices (option state model k default) step wrap?)))

(defn- toggle [state model target]
  (let [current (mode state model)]
    (cond (= target :parameters) (assoc state :display-mode :parameters :display-return :parameters)
          (= target current) (assoc state :display-mode (get state :display-return :parameters) :display-return :parameters)
          :else (cond-> (assoc state :display-mode target :display-return current)
                  (= target :pages) (dissoc :page-bank)))))

(def ^:private mode-actions
  {:display/pages :pages :display/simulator :simulator :display/rig :rig
   :display/parameters :parameters :display/audio :audio :display/block-trace :block-trace})

(defn action-supported? [state action]
  (let [{:keys [modes actions]} (:display-capabilities state)
        action (if (vector? action) (first action) action)
        next-mode (if (= :display/parameter-view action) :parameters (mode-actions action))]
    (and action
         (or (nil? actions) (contains? actions action))
         (or (nil? modes) (nil? next-mode) (contains? modes next-mode)))))

(defn action? [action]
  (or (contains? mode-actions action)
      (contains? #{:display/page-colors :display/previous-bank :display/next-bank
                   :display/parameter-view :display/zoom-in :display/zoom-out :display/camera :display/previous-fixture :display/next-fixture} action)
      (and (vector? action) (= 2 (count action)) (= :display/select-page (first action))
           (nat-int? (second action)) (< (second action) 8))))

(defn- navigate-pages [state model action]
  (if-not (= :pages (mode state model)) state
    (let [{:keys [bank banks pages]} (page-window (page-ids model) (:page-id state) (:page-bank state))]
      (case action
        :display/previous-bank (assoc state :page-bank (max 0 (dec bank)))
        :display/next-bank (assoc state :page-bank (min (dec banks) (inc bank)))
        (if-let [page (get pages (second action))]
          (assoc state :page-id page :origin [0 0] :page-bank bank :last-leds {})
          state)))))

(defn apply-action [state model action]
  (if-let [target (mode-actions action)] (toggle state model target)
    (case action
      :display/page-colors (next-option state model :page-colors page-palettes :both 1 true)
      :display/previous-fixture (update state :fixture-offset (fnil dec 0))
      :display/next-fixture (update state :fixture-offset (fnil inc 0))
      :display/camera (next-option state model :camera camera-lenses :fit 1 true)
      :display/parameter-view (-> state (assoc :display-mode :parameters)
                                  (next-option model :parameter-view parameter-views :auto 1 true))
      :display/zoom-in (next-option state model :history-beats history-spans 4 -1 false)
      :display/zoom-out (next-option state model :history-beats history-spans 4 1 false)
      (if (action? action) (navigate-pages state model action) state))))

(defn view-options [state model]
  (merge (select-keys state [:page-bank :page-colors :camera :fixture-offset :parameter-view :history-beats])
         {:display-mode (mode state model)}))

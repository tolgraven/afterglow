(ns afterglow.control.devices.push-view
  "Push display projection shared by the two tethered control surfaces."
  (:require [afterglow.control.bindings :as bindings]
            [afterglow.control.devices.target-picker :as targets]
            [afterglow.control.display :as display]
            [afterglow.control.pages :as pages]
            [afterglow.control.parameter-edit :as parameter-edit]
            [afterglow.control.views :as views]))

(defn parameter-bank [state instance]
  (let [ids (parameter-edit/ordered-parameters (:definition instance))
        banks (max 1 (long (Math/ceil (/ (count ids) 8.0))))
        index (int (bindings/clamp (get-in state [:parameter-banks (:id instance)] 0) [0 (dec banks)]))
        offset (* 8 index)]
    {:index index :count banks :total (count ids) :offset offset
      :ids (subvec ids (min offset (count ids)) (min (+ offset 8) (count ids)))}))

(defn cue-index [model]
  (let [active (views/active-instances model)]
    {:active active :by-cue (group-by :cue-id active)}))

(defn- cue-at-x [state model x]
  (let [[left bottom] (:origin state)
        cue (pages/cue-id-at model (:page-id state) [(+ left x) bottom])]
    (get-in model [:registry :cues cue])))

(defn- parameter-row [state instance effect k]
  (let [schema (get-in effect [:params k])
        component (get-in state [:components [(:id instance) k]] 0)]
    {:id k :param k :name (or (:name schema) (name k))
      :value (get-in instance [:params k]) :schema schema :component component
      :component-label (nth (parameter-edit/components schema) component)
      :preview-samples (:preview-samples schema)}))

(defn view
  "Build the common Push screen from selected control state and the shared cue index."
  [state model {:keys [active by-cue]} {:keys [status touched-parameter touched-control]}]
  (let [instance (get-in model [:instances (:selected-instance state)])
        bank (parameter-bank state instance)
        active-index (or (first (keep-indexed #(when (= (:id instance) (:id %2)) %1) active)) 0)
        active-offset (* 8 (quot active-index 8))
        cue (get-in model [:registry :cues (:selected-cue state)])
        effect (or (:definition instance) (get-in model [:registry :effects (:effect-id cue)]))
        defaults (merge (into {} (map (fn [[k schema]] [k (:default schema)]) (:params effect)))
                        (:params cue) (:saved-params cue))
        visible (mapv #(cue-at-x state model %) (range 8))
        cue-view (when cue (views/cue-view model (:id cue) by-cue))]
    (merge
     (display/view-options state model)
     {:title "Tolglow" :page (:page-id state) :origin (:origin state)
      :status status
      :master (:master model) :blackout? (:blackout? model)
      :bpm (get-in model [:transport :bpm])
      :selected (:selected-cue state)
      :target-picker (targets/view state)
      :epoch (:epoch model) :frame-number (:frame-number model)
      :instance-id (:id instance) :definition-version (:effect-version instance)
      :parameter-bank (dissoc bank :ids)
      :touched-parameter touched-parameter
      :touched-control touched-control
      :fine? (boolean (:shift? state))
      :preset {:saved? (contains? cue :saved-params)
               :changed? (boolean (and instance (not= defaults (:params instance))))
               :record? (boolean (:record? state))
               :action (if (:shift? state) :clear :save)}
      :active-effect-navigation {:index active-index :count (count active) :offset active-offset}
      :active-effects (mapv #(select-keys % [:id :cue-id :effect-id :order :phase])
                           (take 8 (drop active-offset active)))
      :cue (when cue (select-keys cue-view [:id :name :color :active? :releasing?]))
      :effect (when effect (select-keys effect [:id :name :categories :modifiers :envelope]))
      :swatch (:color cue-view)
      :parameters (mapv #(parameter-row state instance effect %) (:ids bank))
      :cells (mapv #(when % (views/cue-view model (:id %) by-cue)) visible)
      :labels (mapv #(some-> % :id str) visible)})))

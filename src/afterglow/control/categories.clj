(ns afterglow.control.categories
  "Output-derived categories and explicit selectors shared by every control surface.
  Category display colors describe controls; cue swatches describe emitted color."
  (:require [afterglow.render.photometry :as photometry]))

(def colors
  {:color "#c18be8" :intensity "#e8ca74" :movement "#70bedb"
   :beam-shape "#7dcba5" :strobe "#ed8f96" :atmosphere "#91a4bb"
   :modulation "#a4a0ef"})

(defn definition-categories
  "Infer categories from the fields an effect writes, including its native
  transforms. Reading a field as an expression operand does not control it."
  [definition]
  (let [outputs (:outputs definition)
        attributes (into (set (if (map? outputs) (keys outputs) (map :attribute outputs)))
                         (keep :attribute) (get-in definition [:layer :transforms]))]
    (vec (sort-by str
                  (into (set (:categories definition))
                        (cond-> []
                          (or (attributes :color) (some photometry/emitter-spectrum attributes)) (conj :color)
                          (attributes :dimmer) (conj :intensity)
                          (some attributes [:pan :tilt :aim :direction]) (conj :movement)
                          (some attributes [:zoom :focus :iris :gobo]) (conj :beam-shape)
                          (attributes :strobe) (conj :strobe)
                          (attributes :fog) (conj :atmosphere)
                          (:modulation definition) (conj :modulation)))))))

(defn validate-selector
  "Selectors intersect their specified dimensions. Categories match :any (default)
  or :all; an empty dimension selects nothing. An empty map deliberately means all.
  Unknown explicit instance IDs reject rather than silently controlling a subset."
  [model selector]
  (when-not (and (map? selector)
                 (every? #{:categories :match :instance-ids :cue-ids :effect-ids} (keys selector))
                 (#{:any :all} (:match selector :any)))
    (throw (ex-info "Invalid group selector" {:control/error :invalid-selector})))
  (doseq [k [:categories :instance-ids :cue-ids :effect-ids]
          :when (contains? selector k)]
    (let [values (get selector k)]
      (when-not (and (vector? values) (= (count values) (count (set values)))
                     (every? #(if (= k :categories) (keyword? %)
                                  (or (keyword? %) (and (string? %) (seq %)))) values))
        (throw (ex-info "Selector dimensions require vectors of distinct stable IDs"
                        {:control/error :invalid-selector :field k})))))
  (doseq [id (:instance-ids selector)]
    (when-not (contains? (:instances model) id)
      (throw (ex-info "Selected instance no longer exists"
                      {:control/error :unknown-instance :details {:instance-id id}}))))
  selector)

(defn select-instances [model selector]
  (validate-selector model selector)
  (let [dimensions (into {} (map (fn [[k v]] [k (set v)]))
                         (select-keys selector [:instance-ids :cue-ids :effect-ids]))
        wanted (:categories selector)]
    (->> (vals (:instances model))
         (filter (fn [instance]
                   (and (every? (fn [[k values]] (values (get instance ({:instance-ids :id :cue-ids :cue-id :effect-ids :effect-id} k))))
                                dimensions)
                        (or (nil? wanted)
                            (let [actual (set (definition-categories (:definition instance)))]
                              (and (seq wanted)
                                   (if (= :all (:match selector)) (every? actual wanted) (some actual wanted))))))))
         (sort-by (juxt :priority :order :id)) vec)))

(defn group-view [model]
  (let [instances (vals (:instances model))
        categories (sort-by str (set (mapcat #(definition-categories (:definition %)) instances)))]
    (mapv (fn [category]
            (let [members (select-instances model {:categories [category]})]
              {:id category :color (get colors category "#91a4bb")
               :instance-ids (mapv :id members)
               :paused? (every? #(true? (get-in % [:system :paused?])) members)})) categories)))

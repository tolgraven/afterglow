(ns afterglow.control.views
  "Pure device-independent projections. Local focus, menus and raw protocol
  buffers belong to adapters; these views describe committed show state.")

(defn active-instances [model]
  (->> (:instances model) vals (sort-by (juxt :priority :order :id)) vec))

(defn cue-view [model cue-id]
  (when-let [cue (get-in model [:registry :cues cue-id])]
    (let [instances (filterv #(= cue-id (:cue-id %)) (active-instances model))
          active (last instances)]
      {:id cue-id :name (or (:name cue) (str cue-id)) :version (:version cue)
       :effect-id (:effect-id cue) :priority (get cue :priority 0)
       :color (or (get-in active [:params :color]) (:color cue) [0.35 0.35 0.35])
       :active? (boolean (seq instances))
       :releasing? (boolean (and (seq instances) (every? #(= :releasing (:phase %)) instances)))
       :instances (mapv :id instances)
       :params (or (:params active) (:params cue) {})})))

(defn page-view [model page-id]
  (when-let [page (get-in model [:pages page-id])]
    {:id page-id :name (or (:name page) (str page-id))
     :cells (mapv (fn [[[x y] cue-id]] {:x x :y y :cue (cue-view model cue-id)})
                  (sort-by (fn [[[x y] _]] [(- y) x]) (:cells page)))}))

(defn snapshot
  "Public committed control projection. Does not expose resource handles,
  deduplication history, raw definition code or arbitrary private model fields."
  [model]
  (merge (select-keys model [:show-id :epoch :revision :time-ms :master :blackout? :transport])
         {:cues (mapv #(cue-view model %) (sort-by str (keys (get-in model [:registry :cues]))))
          :pages (mapv #(page-view model %) (sort-by str (keys (:pages model))))
          :instances (mapv #(select-keys % [:id :cue-id :effect-id :effect-version :params
                                           :started-at-ms :release-at-ms :duration-ms
                                           :priority :order :phase :launch-mode])
                           (active-instances model))}))

(defn diff-view
  "Return changed and removed top-level values. A transport adds epoch and
  revision checks before applying this bounded projection delta."
  [before after]
  {:set (into {} (filter (fn [[k v]] (or (not (contains? before k)) (not= v (get before k))))) after)
   :remove (into [] (remove #(contains? after %)) (keys before))})

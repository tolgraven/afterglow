(ns afterglow.control.pages
  "Authored pages and the generated recent cue page share one lookup.")

(def recent-page-id
  "Stable virtual page ID, separate from authored keyword and string IDs."
  ["afterglow.control/recent-cues"])

(def ^:private side 8)
(def ^:private limit (* side side))
(def ^:private history-path [:control :recent-cue-ids])

(defn- recent-ids [model]
  (let [ids (get-in model history-path)]
    (if (vector? ids) ids [])))

(defn record-launch [model cue-id]
  (let [ids (recent-ids model)]
    (if (= cue-id (first ids))
      model
      (assoc-in model history-path
                (into [cue-id] (comp (remove #{cue-id}) (take (dec limit))) ids)))))

(defn forget-cue [model cue-id]
  (let [ids (recent-ids model)]
    (if (some #{cue-id} ids)
      (assoc-in model history-path (filterv #(not= cue-id %) ids))
      model)))

(defn page-ids
  "Keep authored page slots in their existing order and append the recent page."
  [model]
  (conj (vec (sort-by str (keys (:pages model)))) recent-page-id))

(defn- available-cue-id [model id]
  (when (get-in model [:registry :cues id]) id))

(defn page
  "Return the authored or generated page with cue IDs keyed by pad coordinate."
  [model page-id]
  (if (= recent-page-id page-id)
    {:id page-id :name "Recent cues" :columns side :rows side
     :cells (into {} (keep-indexed (fn [index id]
                                     (when-let [id (available-cue-id model id)]
                                       [[(mod index side) (- (dec side) (quot index side))] id])))
                  (take limit (recent-ids model)))}
    (get-in model [:pages page-id])))

(defn cue-id-at
  "Resolve a bottom-origin pad coordinate without building a page projection."
  [model page-id [x y :as coordinate]]
  (if (= recent-page-id page-id)
    (when (and (integer? x) (integer? y) (<= 0 x (dec side)) (<= 0 y (dec side)))
      (available-cue-id model (get (recent-ids model) (+ x (* side (- (dec side) y))))))
    (get-in model [:pages page-id :cells coordinate])))

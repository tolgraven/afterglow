(ns afterglow.control.devices.target-picker
  "Device-local one-shot target selection, shared by Push profiles. The show
  supplies its ranked index. Typed selectors pass through to the launch owner.")

(defn toggle [state search model]
  (if (:target-picker state)
    (dissoc state :target-picker)
    (if-not search state
      (let [rows (search model {:kinds [:group :volume :fixture] :text "" :limit 64})]
        (assoc state :target-picker
               {:offset 0 :rows (into [{:kind :default :label "Cue defaults"}]
                                     (comp (filter :selector) (take 64) (map #(select-keys % [:kind :id :label :selector])))
                                     rows)})))))

(defn page [state directions]
  (if-let [{:keys [offset rows]} (:target-picker state)]
    (assoc-in state [:target-picker :offset]
              (max 0 (min (* 8 (quot (dec (count rows)) 8)) (+ offset (* 8 directions)))))
    state))

(defn choose [state column]
  (if-let [{:keys [offset rows]} (:target-picker state)]
    (if-let [row (get rows (+ offset column))]
      (cond-> (dissoc state :target-picker :target-once)
        (:selector row) (assoc :target-once row)) state)
    state))

(defn launch [state result]
  (if (and (:target-once state) (some #(= :cue/launch (:op %)) (:commands result)))
    (-> result (update :state dissoc :target-once)
        (update :commands #(mapv (fn [cmd] (if (= :cue/launch (:op cmd))
                                               (assoc-in cmd [:launch :selector] (get-in state [:target-once :selector])) cmd)) %)))
    result))

(defn view [state]
  (if-let [{:keys [rows offset]} (:target-picker state)]
    {:open? true :page (inc (quot offset 8)) :pages (inc (quot (dec (count rows)) 8))
     :rows (mapv #(select-keys % [:kind :label]) (take 8 (drop offset rows)))}
    (when-let [row (:target-once state)] {:armed (select-keys row [:kind :label])})))

(defn pad [state key [x y]]
  (let [selected (if (zero? y) (choose state x) state)]
    (update selected :picker-pads (fnil conj #{}) key)))

(defn release-pad [state key] (update state :picker-pads disj key))

(defn clear-selection [state] (dissoc state :target-picker :target-once :picker-pads))

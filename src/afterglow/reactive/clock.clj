(ns afterglow.reactive.clock
  "Musical subscriptions over the authoritative, explicit show transport.
  Beat, bar and phrase indices are zero based. No wall clock is consulted."
  (:require [afterglow.reactive :as reactive]
            [afterglow.time :as musical-time]))

(defn- clock [context]
  (let [db @(:db context)
        transport (:transport db)
        beat (double (or (:beat transport) 0.0))]
    (when-not (Double/isFinite beat)
      (throw (ex-info "Reactive transport beat must be finite" {:beat beat})))
    {:beat beat :meter (musical-time/normalize-meter (:meter transport))}))

(defn beat [context _] (long (Math/floor (:beat (clock context)))))

(defn beat-in-bar [context query]
  (let [{:keys [beat meter]} (clock context)]
    (long (mod (Math/floor beat) (:beats-per-bar meter)))))

(defn bar [context _]
  (let [{:keys [beat meter]} (clock context)]
    (long (Math/floor (/ beat (:beats-per-bar meter))))))

(defn phrase [context _]
  (let [{:keys [beat meter]} (clock context)]
    (long (Math/floor (/ beat (* (:beats-per-bar meter) (:bars-per-phrase meter)))))))

(defn phase [context _] (mod (:beat (clock context)) 1.0))

(defn register!
  "Register portable named implementations for the common clock signals."
  [system]
  (doseq [[id handler var-name] [[:clock/beat beat "beat"]
                                [:clock/beat-in-bar beat-in-bar "beat-in-bar"]
                                [:clock/bar bar "bar"] [:clock/phrase phrase "phrase"]
                                [:clock/phase phase "phase"]]]
    (reactive/reg-sub! system id handler
                       {:id id :kind :sub :implementation {:type :var :symbol (str "afterglow.reactive.clock/" var-name)}}))
  system)

(ns capture-push-cue-gesture-543
  (:require [afterglow.control.devices.session :as device]
            [clojure.data.json :as json]
            [clojure.java.io :as io]
            [clojure.test :as test]
            [tolglow.show :as show]))

(defn- pluck-command [command]
  (select-keys command [:op :command-id :cue-id :instance-id :param :value :launch
                        :time-ms :raw :grid :launch-command-id :reason]))

(defn- pending-commands [runtime]
  (mapv (comp pluck-command :payload) (.toArray ^java.util.concurrent.LinkedBlockingQueue (:queue runtime))))

(defn- recorder [run-replay records]
  (fn [options base run!]
    (run-replay options base
      (fn [runtime session input! tick! refresh! sync-input!]
        (let [launches (atom [])
              record! (fn [kind time-ms midi emitted]
                        (let [commands (vec (distinct (concat (pending-commands runtime) (map pluck-command emitted))))
                              local (:local (device/snapshot session))
                              state (:model @(:state runtime))
                              instances (->> (vals (:instances state)) (sort-by :order)
                                             (mapv #(select-keys % [:id :cue-id :phase :launch-mode :params :started-at-ms])))]
                          (swap! launches (fn [previous]
                                           (vec (distinct (into previous (keep #(when (and (= :cue/launch (:op %)) (:grid %))
                                                                                  (:command-id %))) commands)))))
                          (swap! records conj
                                 {:profile (:expression-mode options) :kind kind :time-ms time-ms
                                  :midi midi :commands commands :instances instances
                                  :selection (or (:selected-instance local) (get-in local [:controls :selected-instance]))
                                  :receipts (into [] (keep #(show/quantized-cue-status runtime %)) @launches)})))]
          (run! runtime session
                (fn [at bytes] (let [result (input! at bytes)] (record! :midi at bytes nil) result))
                (fn [at] (let [result (tick! at)] (record! :owner-tick at nil nil) result))
                (fn [at] (let [result (refresh! at)] (record! :profile-refresh at nil nil) result))
                (fn [at bytes]
                  (let [commands (sync-input! at bytes)]
                    (record! :midi-and-owner-tick at bytes commands)
                    commands))))))))

(defn- load-replay-definitions! [path]
  (binding [*ns* *ns*]
    (with-open [source (java.io.PushbackReader. (io/reader path))]
      (loop []
        (let [form (read source false nil)]
          (when (and form (not= 'let (first form)))
            (eval form)
            (recur)))))))

(let [[source capture-path afterglow-head tolglow-head] *command-line-args*
      records (atom [])
      namespace 'push-cue-gesture-replay-543]
  (load-replay-definitions! source)
  (let [run-replay (ns-resolve namespace 'run-replay)
        result (with-redefs-fn {run-replay (recorder @run-replay records)} #(test/run-tests namespace))]
    (when (zero? (+ (:fail result) (:error result)))
      (with-open [writer (io/writer capture-path)]
        (json/write {:afterglow-head afterglow-head :tolglow-head tolglow-head
                     :source "Synthetic MIDI through production Tolglow owner, inert sink"
                     :results (select-keys result [:test :pass :fail :error]) :events @records}
                    writer :escape-slash false)))
    (shutdown-agents)
    (System/exit (if (zero? (+ (:fail result) (:error result))) 0 1))))

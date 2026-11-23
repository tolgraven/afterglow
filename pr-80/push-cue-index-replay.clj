;; Run from the paired Tolglow checkout at a42f441 or later.
;; AFTERGLOW_ROOT=/path/to/candidate lein run -m clojure.main push-cue-index-replay.clj /path/to/baseline /path/to/candidate
;; The fixture uses the source-derived Push 2 transport. No physical MIDI or lighting port is opened.
(require '[tolglow.qa.push-pad-feedback :as qa] '[tolglow.show :as show] '[tolglow.demo :as demo]
         '[tolglow.bench-show :as bench] '[afterglow.control.views :as views] '[afterglow.control.devices.session :as session]
         '[afterglow.control.devices.push-2 :as push] '[tolglow.visualization.cue-pads :as pads]
        )
(defn rig [n]
  (let [rig (reduce #'qa/pad (demo/model) (range 64))]
    (reduce (fn [m i] (bench/command m (keyword (str "launch-" i)) {:op :cue/launch :cue-id (keyword (str "pad-" i))})) rig (range n))))
(defn fixture [n]
  (let [engine (show/create-runtime {:model (rig n) :workspace-options nil :batch? false :worker-timeout-ms 10000})]
    (try (mapv (fn [i] (show/tick! engine (* 25.0 i)) (select-keys @(:state engine) [:model :preview-hdr :variable-observation])) (range 161))
         (finally (show/stop! engine)))))
(defn replay! [frames]
  (let [source (volatile! (first frames)) cpu (#'qa/cpu-clock) recorder (#'qa/midi-recorder)
        sorts (volatile! 0) original views/active-instances display (volatile! [])
        device (session/create {:session-id "capture" :profile (push/profile {})
                 :model! #(:model @source) :now-ms! #(get-in @source [:model :time-ms])
                 :dispatch! (fn [_] (throw (Exception. "No commands expected")))
                 :midi (:midi recorder) :display {:open! (constantly :capture) :render! (fn [_ m] (vswap! display conj m)) :close! (fn [_])}
                 :feedback-source (pads/push-feedback (pads/manager) #(deref source))})]
    (try
      (session/open! device) ((:initialize! recorder)) ((:drain! recorder))
      (with-redefs [views/active-instances (fn [m] (vswap! sorts inc) (original m))]
        (mapv (fn [f]
                (vreset! source f) (vreset! (:messages recorder) []) (vreset! display []) (vreset! sorts 0)
                (let [t (cpu) _ (session/refresh! device) acks ((:drain! recorder)) ms (/ (- (cpu) t) 1e6)]
                  {:elapsed ms :sorts @sorts :acks acks :midi @(:messages recorder) :display @display}))
              (rest frames)))
      (finally (session/close! device)))))
(let [[before after] *command-line-args*]
  (when-not (and before after)
    (throw (ex-info "Pass the baseline and candidate Afterglow checkout directories" {})))
  (try
    (let [frames (fixture 32) baseline (volatile! nil)]
      (doseq [dir [before after after before]]
        (doseq [file ["views.clj" "devices/push_2.clj"]]
          (load-file (str dir "/src/afterglow/control/" file)))
        (let [rows (vec (drop 80 (replay! frames)))
              output (mapv #(select-keys % [:midi :display :acks]) rows)]
          (if @baseline (assert (= @baseline output)) (vreset! baseline output))
          (prn {:checkout dir :frames (count rows)
                :sorts (reduce + (map :sorts rows)) :acks (reduce + (map :acks rows))
                :midi-messages (reduce + (map (comp count :midi) rows))
                :display-publications (reduce + (map (comp count :display) rows))
                :cpu-ms (bench/distribution (map :elapsed rows))}))))
    (finally (shutdown-agents))))

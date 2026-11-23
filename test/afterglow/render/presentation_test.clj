(ns afterglow.render.presentation-test
  (:require [clojure.test :refer [deftest is testing]]
            [afterglow.render.frame :as frame]
            [afterglow.render.presentation :as presentation]))

(def fixtures
  [{:id :pixel :universe 0 :address 1 :channels {:red 1 :green 2 :blue 3 :white 4}}
   {:id :head :universe 0 :address 10
    :channels {:red 1 :green 2 :blue 3 :white 4 :dimmer 5 :pan [6 7] :tilt 8 :focus 9 :strobe 10 :gobo 11}}
   {:id :fine :universe 1 :address 512
    :channels {:dimmer {:offset 1 :fine-offset 2 :inverted-from 0} :pan [4 3]}}])
(def patch (frame/compile-patch fixtures))
(def plan (presentation/compile-plan patch))
(defn a [target attribute value] {:target-id target :attribute attribute :value value})
(def assignments
  [(a :pixel :color [1 0.5 0.25]) (a :pixel :white 0.5)
   (a :head :color [1 0.5 0.25]) (a :head :white 0.5) (a :head :dimmer 0.8)
   (a :head :pan 0.5) (a :head :tilt 0.4) (a :head :focus 0.6) (a :head :strobe 0.3) (a :head :gobo 0.7)
   (a :fine :dimmer 0.5) (a :fine :pan 0.4)])
(defn packet
  ([id time] (packet id time time assignments))
  ([id time completed assignments]
   (presentation/freeze-frame {:epoch 0 :frame-id id :time-ms time :completed-at-ms completed}
                              (frame/resolve-frame patch assignments))))
(defn admitted [state packet] (:state (presentation/complete state packet)))
(defn bytes-at [packet universe & offsets]
  (mapv #(get-in packet [:universes universe (dec %)]) offsets))
(defn frame-at [state time] (:packet (presentation/present state time)))
(defn assert-near [a b] (is (< (Math/abs (double (- a b))) 0.000001)))

(deftest renderer-packet-ownership-is-explicit
  (let [output (frame/resolve-frame patch assignments)
        frozen (presentation/freeze-frame {:epoch 0 :frame-id 1 :time-ms 10 :completed-at-ms 20} output)
        copy-a (presentation/materialize frozen)
        copy-b (presentation/materialize frozen)]
    (aset-byte ^bytes (get-in output [:universes 0]) 0 (byte 0))
    (aset-byte ^bytes (get-in copy-a [:universes 0]) 0 (byte 0))
    (is (= 255 (get-in frozen [:universes 0 0])))
    (is (= 255 (bit-and 255 (aget ^bytes (get-in copy-b [:universes 0]) 0))))
    (is (every? vector? (vals (:universes frozen))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"frozen" (presentation/complete (presentation/new-state plan) output)))
    (is (thrown? clojure.lang.ExceptionInfo (presentation/freeze-frame {:epoch 0 :frame-id 1 :time-ms 20 :completed-at-ms 10} output)))))

(deftest signed-unsigned-and-edited-packets-are-validated
  (let [stamp {:epoch 0 :frame-id 1 :time-ms 0 :completed-at-ms 0}
        state (presentation/new-state (presentation/compile-plan
                                       [{:id :glow :universe 0 :address 1 :channels {:red 1}}]))
        dark (vec (repeat 512 0))
        supplied (into [(byte -128) (short -1) (int 0) (bigint 128) (biginteger 255)] (drop 5 dark))
        frozen (presentation/freeze-frame stamp {:universes {0 supplied}})
        packet (:packet (presentation/present (:state (presentation/complete state frozen)) 0))]
    (is (= [128 255 0 128 255] (subvec (get-in packet [:universes 0]) 0 5)))
    (is (= [-128 -1 0 -128 -1] (take 5 (get-in (presentation/materialize packet) [:universes 0]))))
    (doseq [bad [-129 256 0.5 0.0 nil (inc (bigint Long/MAX_VALUE))]]
      (let [edited (assoc-in frozen [:universes 0 511] bad)]
        (is (thrown? clojure.lang.ExceptionInfo (presentation/complete state edited)) (pr-str bad))
        (is (thrown? clojure.lang.ExceptionInfo (presentation/materialize edited)) (pr-str bad))))
    (doseq [bad [(subvec dark 1) (byte-array 513) (int-array 512)]]
      (is (thrown? clojure.lang.ExceptionInfo (presentation/materialize {:universes {0 bad}}))))))

(deftest direct-default-holds-unmodified-completed-data
  (let [p (packet 1 0 25 assignments)
        state (admitted (presentation/new-state plan) p)]
    (is (= :direct (get-in state [:options :mode])))
    (is (nil? (frame-at state 24)))
    (is (= (:universes p) (:universes (frame-at state 25))))
    (is (= (:universes p) (:universes (frame-at state 10000))))
    (is (= 0 (:time-ms (frame-at state 10000))))
    (is (= 25 (:completed-at-ms (frame-at state 10000))))))

(deftest fade-is-emission-only-and-hardware-dimmer-is-applied-once
  (let [p (packet 1 0)
        state (admitted (presentation/new-state plan {:mode :hold-fade :fade-ms 100}) p)
        half (frame-at state 75)
        dark (frame-at state 125)]
    (is (= (:universes p) (:universes (frame-at state 25))))
    (is (= [128 64 32 64] (bytes-at half 0 1 2 3 4)))
    (is (= [255 128 64 128 102] (bytes-at half 0 10 11 12 13 14)))
    (is (= (bytes-at p 0 15 16 17 18 19 20) (bytes-at dark 0 15 16 17 18 19 20)))
    (is (= [0 0 0 0] (bytes-at dark 0 1 2 3 4)))
    (is (= [255 128 64 128 0] (bytes-at dark 0 10 11 12 13 14)))
    (is (= [255] (bytes-at dark 1 512)))
    (is (= [0] (bytes-at dark 2 1)))
    (is (= 0 (:time-ms half)))
    (is (= 75 (get-in half [:presentation :presented-at-ms])))
    (is (= 0.5 (get-in half [:presentation :gain])))))

(deftest fine-inverted-dimmer-and-reversed-physical-offsets-use-whole-values
  (let [state (admitted (presentation/new-state plan {:mode :hold-fade :fade-ms 100}) (packet 1 0))
        half (frame-at state 75)]
    ;; Renderer fractional-255 convention: inverted half is 127 + 128/255.
    ;; Fade in semantic space to approximately quarter, then invert back.
    (is (= [191] (bytes-at half 1 512)))
    (is (= [64] (bytes-at half 2 1)))
    (is (= [0 102] (bytes-at half 2 2 3)))
    (is (= [127 128] (bytes-at (frame-at state 0) 0 15 16)))))

(deftest one-buffer-interpolation-holds-discrete-controls-until-next-sample
  (let [old (packet 1 0 0 [(a :head :pan 0) (a :head :strobe 0.2) (a :head :gobo 0.3)])
        new (packet 2 25 25 [(a :head :pan 1) (a :head :strobe 0.8) (a :head :gobo 0.9)])
        state (-> (presentation/new-state plan {:mode :buffered-interpolation}) (admitted old) (admitted new))
        half (frame-at state 37.5)]
    (is (nil? (frame-at state 24)))
    (is (= (:universes old) (:universes (frame-at state 25))))
    (is (= [127 128 51 77] (bytes-at half 0 15 16 19 20)))
    (is (= [255 0 204 230] (bytes-at (frame-at state 50) 0 15 16 19 20)))
    (is (= [0 25] (get-in half [:presentation :source-times])))
    (is (= 0.5 (get-in half [:presentation :weight])))
    (is (= 12.5 (get-in half [:presentation :target-time-ms])))))

(deftest interpolation-is-whole-word-not-independent-byte-interpolation
  (let [left (packet 1 0 0 [(a :head :pan (/ 127.99 255))])
        right (packet 2 25 25 [(a :head :pan (/ 128.01 255))])
        state (-> (presentation/new-state plan {:mode :buffered-interpolation}) (admitted left) (admitted right))]
    (is (= [127 252] (bytes-at left 0 15 16)))
    (is (= [128 3] (bytes-at right 0 15 16)))
    (is (= [128 0] (bytes-at (frame-at state 37.5) 0 15 16)))))

(deftest late-completion-keeps-original-time-and-does-not-rewind-output
  (let [state (admitted (presentation/new-state plan {:mode :hold-fade}) (packet 1 0))
        late (packet 2 25 100 assignments)
        with-late (admitted state late)
        before (frame-at with-late 99)
        after (frame-at with-late 100)
        newest (admitted with-late (packet 4 100 110 assignments))
        backwards (presentation/complete newest (packet 3 50 120 assignments))]
    (assert-near 0.26 (get-in before [:presentation :gain]))
    (is (= 25 (:time-ms after)))
    (is (= 100 (:completed-at-ms after)))
    (is (= 0.5 (get-in after [:presentation :gain])))
    (is (= false (:accepted? backwards)))
    (is (= :stale (:reason backwards)))
    (is (= 4 (:frame-id (frame-at (:state backwards) 120))))
    (is (= 3 (:accepted (:state backwards))))))

(deftest buffered-starvation-fades-without-extrapolating-motion
  (let [p (packet 1 0)
        state (admitted (presentation/new-state plan {:mode :buffered-interpolation :fade-ms 100}) p)
        half (frame-at state 100)]
    (is (= 0.5 (get-in half [:presentation :gain])))
    (is (= (bytes-at p 0 15 16 17 18) (bytes-at half 0 15 16 17 18)))
    (is (true? (get-in half [:presentation :fallback?])))
    (is (= [128 64 32 64] (bytes-at half 0 1 2 3 4)))))

(deftest opaque-functions-and-nonlinear-channels-are-never-arbitrarily-moved
  (let [rig [{:id :a :universe 0 :address 1
              :channels {:dimmer {:offset 1 :curve :log}
                         :red 2 :green 3 :blue 4 :pan {:offset 5 :functions [{:range [1 10]}]}
                         :tilt {:offset 6 :inverted-from 10} :focus {:offset 7 :presentation :hold}
                         :zoom {:offset 8 :capabilities []} :strobe 9 :gobo 10}}]
        plan (presentation/compile-plan rig)
        output (frame/resolve-frame rig (mapv #(a :a % 0.8) [:dimmer :red :green :blue :pan :tilt :focus :zoom :strobe :gobo]))
        p (presentation/freeze-frame {:epoch 0 :frame-id 1 :time-ms 0 :completed-at-ms 0} output)
        dark (frame-at (admitted (presentation/new-state plan {:mode :hold-fade}) p) 1000)]
    (is (= #{:red :green :blue} (set (map :attribute (:channels plan)))))
    (is (= [0 0 0] (bytes-at dark 0 2 3 4)))
    (is (= (bytes-at p 0 1 5 6 7 8 9 10) (bytes-at dark 0 1 5 6 7 8 9 10)))))

(deftest admission-and-clock-contracts-bound-history-and-reject-stale-epochs
  (let [state (reduce admitted (presentation/new-state plan) (map #(packet % (* % 25)) (range 10)))
        wrong (assoc (packet 10 250) :epoch 1)
        dropped (presentation/complete state wrong)
        state-at (:state (presentation/present state 300))]
    (is (= [7 8 9] (mapv :frame-id (:history state))))
    (is (= 10 (:accepted state)))
    (is (= :epoch (:reason dropped)))
    (is (= (:history state) (:history (:state dropped))))
    (is (thrown? clojure.lang.ExceptionInfo (presentation/present state-at 299)))
    (is (= (presentation/present state-at 300) (presentation/present state-at 300)))
    (is (thrown? clojure.lang.ExceptionInfo (presentation/new-state plan {:period-ms 0})))
    (is (thrown? clojure.lang.ExceptionInfo (presentation/new-state plan {:latency-ms 51})))
    (is (= :patch (:reason (presentation/complete state (assoc (packet 10 250) :universes {})))))))

(deftest blackout-remains-dark-and-master-is-not-reapplied
  (let [output (frame/resolve-frame patch assignments {:master 0.5})
        p (presentation/freeze-frame {:epoch 0 :frame-id 1 :time-ms 0 :completed-at-ms 0} output)
        half (frame-at (admitted (presentation/new-state plan {:mode :hold-fade}) p) 75)
        blackout (presentation/freeze-frame {:epoch 0 :frame-id 2 :time-ms 25 :completed-at-ms 25}
                                           (frame/resolve-frame patch assignments {:blackout? true}))
        dark (frame-at (admitted (presentation/new-state plan {:mode :hold-fade}) blackout) 1000)]
    (is (= [64 32 16 32] (bytes-at half 0 1 2 3 4)))
    (is (= [51] (bytes-at half 0 14)))
    (is (= [0 0 0 0 0] (bytes-at dark 0 10 11 12 13 14)))
    (is (= (bytes-at blackout 0 15 16 17 18 19 20) (bytes-at dark 0 15 16 17 18 19 20)))))

(deftest supplemental-emitters-interpolate-and-fade-in-semantic-space
  (let [emitters [:warm-white :cold-white :cool-white :amber :cyan :lime :uv]
        channels (zipmap emitters (range 1 8))
        fixtures [{:id :bare :address 1 :universe 0 :channels (assoc channels :fog 8)}
                  {:id :dimmer :address 10 :universe 0 :channels (assoc channels :dimmer 8)}]
        plan (presentation/compile-plan fixtures)
        make-frame (fn [id time level]
                     (let [rows (vec (for [f fixtures, ch (keys (:channels f))] (a (:id f) ch level)))]
                       (presentation/freeze-frame {:epoch 0 :frame-id id :time-ms time :completed-at-ms time}
                                                  (frame/resolve-frame fixtures rows))))
        full (make-frame 1 0 1.0)
        faded (frame-at (admitted (presentation/new-state plan {:mode :hold-fade :fade-ms 100}) full) 75)
        mid (frame-at (-> (presentation/new-state plan {:mode :buffered-interpolation})
                          (admitted (make-frame 1 0 0.0)) (admitted (make-frame 2 25 1.0))) 37.5)]
    (is (= (repeat 7 128) (apply bytes-at faded 0 (range 1 8))))
    (is (= (repeat 7 255) (apply bytes-at faded 0 (range 10 17))))
    (is (= [255 128] (bytes-at faded 0 8 17)))
    (is (= (repeat 7 128) (apply bytes-at mid 0 (range 1 8))))
    (is (= (repeat 8 128) (apply bytes-at mid 0 (range 10 18))))
    (is (= [0] (bytes-at mid 0 8)))))

(ns afterglow.render.edge-tracking-test
  (:require [afterglow.render.frame :as frame]
            [afterglow.render.gpu.movement :as movement]
            [afterglow.render.optics :as optics]
            [clojure.test :refer [deftest is]]))

(def floor {:id :floor :point [0 0 0] :normal [0 1 0] :size [40 40]})
(def links [{:leader :one :follower :two :surface floor :along [1 0 0]}
            {:leader :two :follower :three :surface floor :along [1 0 0]}])
(def heads (mapv (fn [id x address angle]
                   {:id id :position [x 3 -1] :beam-angle angle :lens-radius-m 0.1
                    :universe 1 :address address :channels {:pan [1 2] :tilt [3 4] :red 5 :green 6 :blue 7}})
                 [:one :two :three] [-2 1 4] [510 518 526] [25 22 19]))
;; Express fixture addresses within their own universe even when a coarse/fine
;; pair or the fixture as a whole crosses a boundary.
(def rig (mapv (fn [f] (if (> (:address f) 512)
                         (-> f (update :address - 512) (update :universe inc)) f)) heads))
(defn- assign [id key value] {:target-id id :attribute key :value value})
(defn- authored [x]
  (into [(assign :one :aim [(- x 1.0) 0.0 1.0])
         (assoc (assign :one :aim [(+ x 1.0) 0.0 1.0]) :opacity 0.5)]
        (for [f rig] (assign (:id f) :color [1.0 0.4 0.2]))))
(defn- spots [patch rows]
  (mapv (fn [f]
          (let [row (get rows (:id f))
                beam (optics/fixture-beam f (assoc row :pose (frame/fixture-pose f row)))]
            (optics/beam-footprint beam floor))) (:fixtures patch)))
(defn- x-extents [spot]
  (let [x (first (:center spot))
        width (Math/hypot (* (:major-radius-m spot) (first (:major-axis spot)))
                          (* (:minor-radius-m spot) (first (:minor-axis spot))))]
    [(- x width) (+ x width)]))
(defn- near [a b] (< (abs (- a b)) 1.0e-8))

(deftest chains-track-actual-post-blend-movement-every-frame
  (let [patch (frame/compile-patch rig)]
    (doseq [rich? [true false]]
      (loop [xs [-2.0 -1.4 -0.7 0.0], previous nil]
        (when-let [x (first xs)]
          (let [out (frame/resolve-frame patch (authored x)
                                         {:edge-tracking links :include-values? rich? :compact-values? true
                                          :previous-compact previous})
                rows (or (:values out) (into {} (map (juxt :id identity)) (frame/project-compact (:compact out))))
                [a b c] (spots patch rows)]
            (is (every? :contact (:edge-tracking out)))
            (is (near x (first (:hit a))))
            (is (near (second (x-extents a)) (first (x-extents b))))
            (is (near (second (x-extents b)) (first (x-extents c))))
            (is (= 255 (bit-and 255 (aget ^bytes (get-in out [:universes 2]) 1))))
            (recur (next xs) (:compact out))))))))

(deftest unreachable-targets-suppress-only-their-followers-and-recover
  (let [patch (frame/compile-patch rig)
        blocked-rig (assoc-in rig [1 :calibration :tilt] {:min-deg 0 :max-deg 70})
        result (frame/resolve-contributions blocked-rig [{:kind :assignments :assignments (authored -2)}]
                                            {:edge-tracking links})]
    (is (= [:unreachable :leader-suppressed] (mapv :reason (:edge-tracking result))))
    (is (= [0.0 0.0 0.0] (get-in result [:values :two :emitted-color]) (get-in result [:values :three :emitted-color])))
    (is (= [1.0 0.4 0.2] (get-in result [:values :one :emitted-color])))
    (let [miss (frame/resolve-frame patch (conj (authored -2) (assign :one :aim [0 8 1])) {:edge-tracking links})
          restored (frame/resolve-frame patch (authored -2) {:edge-tracking links :previous-values (:values miss)})]
      (is (= :missed-receiver (get-in miss [:edge-tracking 0 :reason])))
      (is (= [1.0 0.4 0.2] (get-in restored [:values :two :emitted-color]))))
    (is (= :missing-leader (-> (frame/resolve-frame patch [] {:edge-tracking [(assoc (first links) :leader :gone)]})
                               :edge-tracking first :reason)))
    (is (thrown? clojure.lang.ExceptionInfo
                 (frame/resolve-frame patch [] {:edge-tracking [(first links) (assoc (first links) :leader :two :follower :one)]})))))

(deftest native-path-and-reference-capture-identical-tangent-axes
  (let [patch (frame/compile-patch rig)
        blocks [{:kind :assignments :assignments (authored -1.0)}]
        opts {:edge-tracking links :include-values? false :compact-values? true}
        plain (frame/resolve-contributions patch blocks opts)
        plan (frame/prepare-movement-frame patch blocks opts)]
    (is (= #{:one :two :three} (:reference-ids plan)))
    (is (every? some? (map (:targets plan) (:reference-ids plan))))
    (with-open [owner (movement/open!)]
      (let [moved (movement/resolve-contributions! owner patch blocks opts)]
        (is (= 0 (get-in moved [:movement :gpu-heads])))
        (is (= (:edge-tracking plain) (:edge-tracking moved)))
        (doseq [[u bytes] (:universes plain)]
          (is (= (seq bytes) (seq (get-in moved [:universes u])))))))))

(deftest constrained-links-use-the-actual-leading-mechanical-stop
  (let [limited (assoc-in rig [0 :calibration :pan] {:min-deg -5.0 :max-deg 5.0})
        patch (frame/compile-patch limited)
        result (frame/resolve-frame patch (authored 2.0) {:edge-tracking links})
        [a b] (spots patch (:values result))]
    (is (false? (get-in result [:values :one :aim-reachable?])))
    (is (> (abs (- 2.0 (first (:hit a)))) 1))
    (is (near (second (x-extents a)) (first (x-extents b))))))

(def collision-rig
  (mapv (fn [i id]
          {:id id :position [i 3 0] :beam-angle 20 :lens-radius-m 0.1
           :universe 1 :address (+ 1 (* i 11)) :channels (:channels (first rig))})
        (range 4) [:one :two :three :four]))

(defn- collision-assignments [third-x]
  (into [(assign :one :aim [0 0 0]) (assign :three :aim [third-x 0 0])]
        (map #(assign (:id %) :color [1.0 0.4 0.2]))
        collision-rig))

(deftest later-followers-yield-when-their-spots-overlap
  (let [leader (first links)
        sibling (assoc leader :follower :three)
        dependent (assoc leader :leader :three :follower :four)
        parallel-plane (assoc floor :id :platform :point [0 0.5 0])]
    (doseq [rich? [true false]]
      (let [options {:include-values? rich? :compact-values? (not rich?)}
            run (fn [links] (frame/resolve-frame collision-rig (collision-assignments 2)
                                               (assoc options :edge-tracking links)))
            conflict (run [leader sibling dependent])
            reversed (run [sibling leader])
            separate (run [leader (assoc sibling :surface parallel-plane)])
            red (fn [frame] (mapv #(bit-and 255 (aget ^bytes (get-in frame [:universes 1]) %))
                                  [4 15 26 37]))]
        (is (= [nil :overlap :leader-suppressed] (mapv :reason (:edge-tracking conflict))))
        (is (= [255 255 0 0] (red conflict)))
        (is (= [nil :overlap] (mapv :reason (:edge-tracking reversed))))
        (is (= [255 0 255 255] (red reversed)))
        (is (every? :contact (:edge-tracking separate)))
        (is (= [255 255 255 255] (red separate)))))))

(deftest a-moving-leader-can-clear-space-for-a-suppressed-follower
  (let [link (first links)
        other (assoc link :leader :three :follower :four)
        options {:edge-tracking [link other] :compact-values? true}
        blocked (frame/resolve-frame collision-rig (collision-assignments 1.45) options)
        clear (frame/resolve-frame collision-rig (collision-assignments 4)
                                  (assoc options :previous-compact (:compact blocked)))]
    (is (= [:overlap nil] (mapv :reason (:edge-tracking blocked))))
    (is (= [0.0 0.0 0.0] (get-in blocked [:values :two :emitted-color])))
    (is (every? :contact (:edge-tracking clear)))
    (is (= [1.0 0.4 0.2] (get-in clear [:values :two :emitted-color])))))

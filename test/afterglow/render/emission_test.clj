(ns afterglow.render.emission-test
  (:require [afterglow.render.emission :as emission]
            [afterglow.render.frame :as frame]
            [clojure.test :refer [deftest is]]))

(def fixtures
  [{:id :head :channels {:red 1 :white 2 :dimmer {:offset 3 :fine-offset 4 :inverted-from 33.75}
                         :strobe 5 :pan 6 :shutter 7} :universe 0 :address 510}
   {:id :strip :channels {:red 1 :blue 2} :universe 1 :address 8}
   {:id :fog :channels {:dimmer 1 :fog 2} :universe 2 :address 1}
   {:id :spot :channels {:dimmer 1} :emission-color [0.5 1 0.5] :universe 2 :address 4}])
(def patch (frame/compile-patch fixtures))
(defn head [id] (get-in patch [:by-id id]))
(defn row [id a v] {:target-id id :attribute a :value v})
(def rows [(row :head :red 0.7) (row :head :white 0.1) (row :head :dimmer 0.8)
           (row :head :pan 0.4) (row :head :strobe 0.9) (row :head :shutter 0.25)
           (row :strip :red 0.7) (row :strip :blue 0.3) (row :spot :dimmer 1)
           (row :fog :dimmer 1) (row :fog :fog 0.35)])
(defn near? [a b] (< (abs (- a b)) 0.005))
(defn freeze [f] (update-vals (:universes f) vec))

(deftest absent-and-nil-inversions-produce-identical-frames
  (doseq [attr [:red :dimmer] fine [nil 2]]
    (let [channel (cond-> {:offset 1} fine (assoc :fine-offset fine))
          render (fn [spec]
                   (let [p (frame/compile-patch [{:id :lamp :address 512 :universe 0
                                                  :channels {attr spec}}])
                         source (frame/resolve-frame p [(row :lamp attr 0.75)] {})]
                     [(freeze source) (freeze (emission/scale-emission p source {:lamp 0.4}))]))]
      (is (= (render channel) (render (assoc channel :inverted-from nil)))))))

(deftest uncolored-lamps-use-white-in-every-output-projection
  (let [fixture {:id :lamp :address 1 :universe 0 :channels {:dimmer 1}}
        render (fn [f]
                 (let [patch (frame/compile-patch [f])
                       input (frame/resolve-frame patch [(row :lamp :dimmer 1)] {:compact-values? true})
                       scaled (emission/scale-emission patch input {:lamp 0.5})]
                   [(freeze scaled) (get-in scaled [:values :lamp :emitted-color])
                    (:emitted-color (first (frame/project-compact (:compact scaled))))]))]
    (is (= (render fixture) (render (assoc fixture :emission-color nil))
           (render (assoc fixture :emission-color [1.0 1.0 1.0]))))))

(deftest scaled-output-meets-budget-without-changing-other-channels
  (doseq [compact? [false true]]
    (let [source (frame/resolve-frame patch rows {:master 0.65 :include-values? (not compact?) :compact-values? compact?})
          bytes (freeze source)
          request {:head 0.4 :strip 0.6 :spot 0.2 :fog 0.0}
          out (emission/scale-emission patch source request)
          rgb (:red (emission/emitted-levels (head :head) out))
          view (if compact? (first (frame/project-compact (:compact out))) (get-in out [:values :head]))]
      (is (= bytes (freeze source)))
      (is (identical? source (emission/scale-emission patch source {:head 1.0})))
      (is (nil? (emission/levels (head :fog) out)))
      (doseq [id [:head :strip :spot]
              [attr before] (emission/emitted-levels (head id) source)]
        (let [after (get (emission/emitted-levels (head id) out) attr)]
          (is (<= after (* before (request id))))
          (is (near? after (* before (request id))))))
      (is (near? (:intensity view) (:dimmer (emission/levels (head :head) out))))
      (is (near? (first (:emitted-color view)) (+ rgb (:white (emission/emitted-levels (head :head) out)))))
      (is (= (subvec (get bytes 1) 1 4) (subvec (get (freeze out) 1) 1 4)))
      (is (= (subvec (get bytes 2) 0 2) (subvec (get (freeze out) 2) 0 2))))))

(deftest colored-release-survives-a-dark-input-frame
  (let [idle (frame/resolve-frame patch [] {:include-values? false :compact-values? true})
        before (frame/project-compact (:compact idle))
        release (emission/with-emitted-levels patch idle {:head {:red 0.2 :white 0.0}})
        view (first (frame/project-compact (:compact release)))]
    (is (near? 0.2 (:red (emission/emitted-levels (head :head) release))))
    (is (near? 0.2 (first (:emitted-color view))))
    (is (= before (frame/project-compact (:compact idle))))
    (is (thrown? Exception (emission/with-emitted-levels patch idle {:head {:pan 0.5}})))))

(deftest fractional-inversions-never-exceed-the-accepted-budget
  (doseq [pivot [nil 0 0.2 63.25 254.8] fine [nil 2]]
    (let [p (frame/compile-patch [{:id :lamp :channels {:dimmer (cond-> {:offset 1}
                                                                fine (assoc :fine-offset fine)
                                                                pivot (assoc :inverted-from pivot))}
                                   :address 512 :universe 1}])
          f (get-in p [:by-id :lamp])
          maximum (frame/resolve-frame p [(row :lamp :dimmer 1.0)] {})
          full (:dimmer (emission/levels f maximum))]
      (doseq [gain (map #(/ % 135.0) (range 136))]
        (let [out (emission/scale-emission p maximum {:lamp gain})
              delivered (:dimmer (emission/levels f out))]
          (is (<= 0.0 delivered (* full gain)))
          (is (< (- (* full gain) delivered) (/ 1.01 (if fine 65535.0 255.0)))))))))

(deftest packed-gain-columns-and-followers-share-the-rich-emission-contract
  (let [gains (double-array [0.16 0.4 1.0 0.77])
        fixtures (:fixtures patch)
        target (zipmap (:target-order patch) (seq gains))]
    (doseq [compact? [false true]]
      (let [options {:include-values? (not compact?) :compact-values? compact?}
            src (frame/resolve-frame patch rows options)
            zero (frame/resolve-frame patch [] options)
            before (freeze src)
            on (emission/follow-frame patch src nil zero 0.25 0.4 1.0)
            original (vec (:levels on))
            expected (emission/with-emitted-levels patch src
                       (into {} (for [f fixtures :let [levels (emission/emitted-levels f src)] :when levels]
                                  [(:id f) (update-vals levels #(* 0.25 %))])))
            ;; Keep a full precision copy of the previous frame's emitted
            ;; channels while lowering the requested front/strip levels.
            tail (emission/follow-frame patch zero (:levels on) nil
                                        (double-array [1 1 -1 1]) (double-array [0.4 0.25 -1 1]) 1.0)
            old-head (:red (emission/emitted-levels (head :head) (:frame on)))
            new-head (:red (emission/emitted-levels (head :head) (:frame tail)))]
        (is (= before (freeze src)))
        (is (= original (vec (:levels on))))
        (is (= (freeze (emission/scale-emission patch src target))
               (freeze (emission/scale-emission patch src gains))))
        (is (= (freeze expected) (freeze (:frame on))))
        (is (near? new-head (* 0.6 old-head)))
        (is (= 0.0 (:dimmer (emission/emitted-levels (head :spot) (:frame tail)))))
        (is (identical? src (:frame (emission/follow-frame patch src nil src 0.1 0.1 1)))))))
  (is (thrown? Exception (emission/scale-emission patch (frame/resolve-frame patch [] {}) (double-array [1])))))

(deftest exact-ramps-track-each-emitter-independently-across-retargeting
  (let [aim (fn [r b]
              (frame/resolve-frame patch [{:target-id :strip :attribute :red :value r}
                                          {:target-id :strip :attribute :blue :value b}]
                                   {:include-values? false :compact-values? true}))
        follow (fn [previous target step]
                 (emission/follow-frame patch target (:levels previous) nil step step 1.0
                                        {:attack true :release true :previous (:ramps previous)}))
        levels #(emission/emitted-levels (head :strip) (:frame %))
        next (follow nil (aim 1.0 0.0) 0.25)
        first-levels (vec (:levels next))
        mixed (follow next (aim 1.0 1.0) 0.25)
        done (follow mixed (aim 1.0 1.0) 0.5)]
    (is (= (levels mixed) {:red (/ 128.0 255) :blue (/ 64.0 255)}))
    (is (= (levels done) {:red 1.0 :blue (/ 191.0 255)}))
    (is (= {:red 1.0 :blue 1.0} (levels (follow done (aim 1.0 1.0) 0.25))))
    (is (= first-levels (vec (:levels next))))))

(deftest a-color-change-can-leave-a-release-tail-at-the-same-overall-level
  (let [look (fn [attr] (frame/resolve-frame patch [{:target-id :strip :attribute attr :value 1.0}] {}))
        red (look :red) blue (look :blue)
        falling (emission/falling-heads patch red blue)]
    (is (= #{:strip} (set (map first (filter second (map vector (:target-order patch) falling))))))
    (is (not-any? true? (seq (emission/falling-heads patch blue blue))))))


(deftest feedback-reads-the-entire-delivered-fine-dimmer-word
  (let [patch (frame/compile-patch [{:id :head :address 512 :universe 1 :channels {:dimmer [1 2]}}])
        head (first (:fixtures patch))]
    (doseq [code [0 254 255 256 32767 32768 65534 65535]]
      (let [expected (/ code 65535.0)
            result (frame/resolve-frame patch [{:target-id :head :attribute :dimmer :value expected}])]
        (is (< (abs (- expected (:dimmer (emission/emitted-levels head result)))) 1e-12))))))

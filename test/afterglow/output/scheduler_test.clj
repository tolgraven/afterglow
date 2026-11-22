(ns afterglow.output.scheduler-test
  (:require [clojure.test :refer [deftest is]]
            [afterglow.render.frame :as render]
            [afterglow.output.retirement :as retirement]
            [afterglow.output.scheduler :as scheduler]))

(def fixtures [{:id :pixel :universe 0 :address 1 :channels {:red 1 :green 2 :blue 3}}])
(def patch (delay (render/compile-patch fixtures)))
(defn- bytes-copy [universes]
  (into {} (map (fn [[u data]] [u (mapv #(bit-and (int %) 255) data)])) universes))
(defn- capture [physical sent]
  (scheduler/create {:now-ms #(deref physical)
                     :send! (fn [universes id] (swap! sent conj {:id id :bytes (bytes-copy universes)}))}))
(defn- frame [r g b]
  {:universes {0 (byte-array (concat (map unchecked-byte [r g b]) (repeat 509 0)))}})

(deftest deadline-fallback-is-independent-from-completion-and-preserves-original-time
  (let [physical (atom 0) sent (atom []) owner (capture physical sent)
        token (scheduler/begin-frame! owner 0 @patch {:mode :hold-fade} false)
        output (frame 200 100 50)]
    (try
      (scheduler/complete! owner token output)
      ;; Mutation by a renderer reusing its private output cannot leak through.
      (aset-byte ^bytes (get-in output [:universes 0]) 0 (byte 0))
      (scheduler/publish! owner)
      (is (= [200 100 50] (subvec (get-in (last @sent) [:bytes 0]) 0 3)))
      (reset! physical 25)
      (let [late (scheduler/begin-frame! owner 0 @patch {:mode :hold-fade} false)]
        (reset! physical 75)
        (scheduler/publish! owner)
        (is (= [100 50 25] (subvec (get-in (last @sent) [:bytes 0]) 0 3)))
        (reset! physical 100)
        (scheduler/complete! owner late (frame 100 80 40))
        (scheduler/publish! owner)
        (is (= [25 nil] (get-in (scheduler/status owner) [:last :source-times])))
        (is (= [50 40 20] (subvec (get-in (last @sent) [:bytes 0]) 0 3))))
      (finally (scheduler/close! owner)))))

(deftest epochs-blackout-and-close-fence-buffered-bright-output
  (let [physical (atom 0) sent (atom []) owner (capture physical sent)
        token (scheduler/begin-frame! owner 0 @patch {} false)]
    (scheduler/complete! owner token (frame 255 100 10))
    (scheduler/publish! owner)
    (reset! physical 25)
    (let [new-token (scheduler/begin-frame! owner 1 @patch {} false)]
      (is (nil? (scheduler/complete! owner token (frame 255 255 255))))
      (scheduler/publish! owner)
      (is (every? zero? (get-in (last @sent) [:bytes 0])))
      (scheduler/complete! owner new-token (frame 40 80 120))
      (scheduler/publish! owner)
      (is (= [40 80 120] (subvec (get-in (last @sent) [:bytes 0]) 0 3)))
      (reset! physical 50)
      (scheduler/begin-frame! owner 1 @patch {} true)
      (scheduler/publish! owner)
      (is (every? zero? (get-in (last @sent) [:bytes 0])))
      (scheduler/close! owner)
      (let [n (count @sent)]
        (is (nil? (scheduler/complete! owner new-token (frame 255 255 255))))
        (scheduler/publish! owner)
        (is (= n (count @sent)))))))

(deftest pending-completions-are-bounded-and-coalesce-oldest
  (let [physical (atom 0) sent (atom []) owner (capture physical sent)]
    (try
      (dotimes [n 12]
        (reset! physical n)
        (scheduler/complete! owner (scheduler/begin-frame! owner 0 @patch {} false) (frame n 0 0)))
      (is (= 3 (:pending (scheduler/status owner))))
      (is (= 9 (:coalesced (scheduler/status owner))))
      (scheduler/publish! owner)
      (is (= 11 (get-in (last @sent) [:bytes 0 0])))
      (finally (scheduler/close! owner)))))

(deftest waiting-and-blackout-present-the-configured-fog-off
  (let [sent (atom []) now (atom 0)
        nozzle {:id :fog :universe 3 :address 512 :channels {:fog {:offset 1 :fine-offset 2 :inverted-from 32}}
                :fogger {:flow-m3-min 60 :dmx-range [196.5 5]}}
        owner (scheduler/create {:now-ms #(deref now)
                                 :send! (fn [buffers _] (swap! sent conj
                                                              (mapv #(bit-and 255 (get-in buffers %)) [[3 511] [4 0]])))})
        patch (render/compile-patch [nozzle])
        token (scheduler/begin-frame! owner 0 patch {} false)]
    (scheduler/publish! owner)
    (scheduler/complete! owner token (render/resolve-frame patch [{:target-id :fog :attribute :fog :value 1.0}]))
    (scheduler/publish! owner)
    (scheduler/begin-frame! owner 0 patch {} true)
    (scheduler/publish! owner)
    (is (= [[196 128] [32 0] [196 128]] @sent))
    (scheduler/close! owner)))


(deftest retired-pumps-hold-off-until-a-new-fixture-claims-the-slot
  (let [fog {:id :fog :universe 3 :address 512 :channels {:fog [1 2]}
             :fogger {:flow-m3-min 60 :dmx-range [196.5 0]}}
        old (render/compile-patch [fog])
        survivor {:id :light :universe 3 :address 7 :channels {:dimmer 1}}
        next (render/compile-patch [survivor])
        plan (retirement/plan nil old next)
        raw (render/idle-universes next)
        delivery #(retirement/include-retired plan raw)
        physical #(bit-and 255 (get-in %1 %2))]
    (is (= 196 (physical (delivery) [3 511])))
    (is (= 128 (physical (delivery) [4 0])))
    (is (zero? (physical raw [3 511])) "Rendering keeps the original array.")
    (aset-byte ^bytes (get (delivery) 4) 0 (byte 2))
    (is (= 128 (physical (delivery) [4 0])) "The next packet owns its bytes.")
    (let [claimed (render/compile-patch [(assoc survivor :address 511 :footprint 3)])
          plan (retirement/plan plan next claimed)
          packet (retirement/include-retired plan (render/idle-universes claimed))]
      (is (zero? (physical packet [3 511])))
      (is (zero? (physical packet [4 0]))))))

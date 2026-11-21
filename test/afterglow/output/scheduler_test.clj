(ns afterglow.output.scheduler-test
  (:require [clojure.test :refer [deftest is]]
            [afterglow.render.frame :as render]


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

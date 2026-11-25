(ns afterglow.spatial-test
  (:require [afterglow.spatial :as spatial]
            [clojure.edn :as edn]
            [clojure.test :refer [deftest is testing]]))

(def bounds {:min [-2 0 -2] :max [2 4 2]})

(def rig [{:id :a :position [0 2 0]} {:id :b :position [1 2 0]}])

(def ball {:shape :ball :radius 0.2 :position [0 2 0] :velocity [10 0 0]
           :restitution 1.0 :hardness 0.4 :angular-velocity [0 2 0]})

(defn scene [volumes] {:bounds bounds :gravity [0 0 0] :volumes volumes})

(defn tick [prior settings t]
  (spatial/advance (:state prior) settings {:time-ms t :epoch 2} rig {}))

(defn near [a b] (< (abs (- a b)) 1e-8))

(deftest deterministic-throw-events-motion-and-release
  (let [settings (spatial/prepare (scene {:ball ball}))
        start (tick nil settings 0)
        step (tick start settings 250)
        run (reduce #(tick %1 settings %2) start (range 25 251 25))]
    (is (= {:ball #{:a}} (:members start)))
    (is (= [{:type :spatial/enter :fixture-id :a :volume-id :ball :time-ms 0}] (:events start)))
    (is (= (:state step) (:state run)))
    (is (= (:state step) (edn/read-string (pr-str (:state step)))))
    (is (near 1.1 (first (get-in step [:signals :ball :position]))))
    (is (= [-1.0 0.0 0.0] (get-in step [:signals :ball :direction])))
    (is (near 0.5 (get-in step [:signals :ball :rotation 1])))
    (is (pos? (get-in step [:signals :ball :deformation])))
    (is (= [[:spatial/exit :a] [:spatial/enter :b] [:spatial/exit :b] [:spatial/bounce nil] [:spatial/enter :b]]
           (mapv (juxt :type :fixture-id) (:events step))))
    (let [bounce (first (filter #(= :spatial/bounce (:type %)) (:events step)))]
      (is (= [:x :max] (:surface bounce)))
      (is (near 180.0 (:time-ms bounce))))
    (is (= #{:b} (get-in step [:members :ball])))
    (is (= [:spatial/exit] (mapv :type (:events (tick step (scene {}) 275)))))))

(deftest shape-composition-hdr-fields-and-rig-edits
  (let [box {:shape :box :min [-1 1 -1] :max [1 3 1]}
        hole {:shape :cylinder :position [1 2 0] :height 4 :radius 0.05}
        shapes {:box box :cut {:shape :difference :parts [box hole]} :both {:shape :union :parts [box hole]}
                :plane {:shape :polyhedron :planes [{:normal [1 0 0] :distance 0.5}]}
                :bloom {:shape :hdr :source-id :a :threshold 0.1}}
        settings (scene shapes)
        run #(spatial/advance %1 settings {:time-ms %2} (spatial/prepare-rig %3) %4)
        entry (run nil 0 rig {:a {:b 0.2} :third {:a 0.3}})]
    (is (= {:box #{:a :b} :cut #{:a} :both #{:a :b} :plane #{:a} :bloom #{:b}} (:members entry)))
    (let [next (run (:state entry) 25 [(second rig)] {:a {:b 0.1} :third {:b 1.0}})]
      (is (= #{:a :b} (set (map :fixture-id (:events next)))))
      (is (every? #(= :spatial/exit (:type %)) (:events next)))
      (is (= #{} (get-in next [:members :bloom]))))))

(deftest elastic-collision-and-mutual-attraction
  (let [a (assoc ball :position [-0.3 2 0] :velocity [1 0 0])
        b (assoc ball :position [0.3 2 0] :velocity [-1 0 0])
        settings (scene {:a a :b b})
        result (tick (tick nil settings 0) settings 150)]
    (is (= [-1.0 0.0 0.0] (get-in result [:signals :a :velocity])))
    (is (= [1.0 0.0 0.0] (get-in result [:signals :b :velocity])))
    (is (= #{[:a :b] [:b :a]}
           (set (map (juxt :volume-id :other-id) (filter :other-id (:events result)))))))
  (let [anchored (assoc ball :position [1 2 0] :fixed? true :attraction 4)
        settings (scene {:well anchored :orb (assoc ball :velocity [0 0 1])})
        result (tick (tick nil settings 0) settings 100)]
    (is (= [1.0 2.0 0.0] (mapv double (get-in result [:signals :well :position]))))
    (is (pos? (get-in result [:signals :orb :velocity 0])))
    (is (pos? (get-in result [:signals :orb :velocity 2])))))

(deftest suspension-restore-resize-rethrow-and-bounded-stall
  (let [settings (scene {:orb ball})
        initial (tick nil settings 0)
        before (tick initial settings 10)
        asleep (spatial/rebase (:state before) {:time-ms 100010 :epoch 9})
        resumed (spatial/advance asleep settings {:time-ms 100010 :epoch 9} rig {})
        bigger (tick before (assoc-in settings [:volumes :orb :radius] 0.5) 10)
        thrown (tick bigger (assoc-in settings [:volumes :orb :throw-id] 2) 10)
        paused (spatial/advance (:state before) settings {:time-ms 100 :epoch 2 :playing? false} rig {})
        playing (spatial/advance (:state paused) settings {:time-ms 5000 :epoch 2 :playing? true} rig {})]
    (is (= (:signals before) (:signals resumed) (:signals paused) (:signals playing)))
    (is (empty? (:events resumed)))
    (is (= 0.5 (get-in bigger [:signals :orb :radius])))
    (is (= (get-in before [:signals :orb :position]) (get-in bigger [:signals :orb :position])))
    (is (= [0 2 0] (get-in thrown [:signals :orb :position])))
    (is (near 9600.0 (:dropped-ms (tick initial settings 10000))))
    (is (nil? (spatial/rebase nil {:time-ms 0})))))

(deftest invalid-physics-and-shapes-are-rejected-before-install
  (doseq [bad [(assoc ball :radius -1) (assoc ball :velocity [##NaN 0 1])
               (assoc ball :radius 3) (assoc ball :restitution 1.1)
               {:shape :box :min [0 0 0] :max [0 2 3]}
               {:shape :intersection :parts []} {:shape :hdr :threshold ##Inf}]]
    (is (thrown? clojure.lang.ExceptionInfo (spatial/prepare (scene {:bad bad}))))))

(deftest fast-throw-can-enter-and-leave-between-two-rendered-frames
  (let [s (scene {:needle (assoc ball :radius 0.01 :position [-0.5 2 0] :velocity [220 0 0])})
        r (tick (tick nil s 0) s 5)
        hits (filter #(= :a (:fixture-id %)) (:events r))]
    (is (= #{} (get-in r [:members :needle])))
    (is (= [:spatial/enter :spatial/exit] (mapv :type hits)))
    (is (< 0 (:time-ms (first hits)) (:time-ms (last hits)) 5))))

(deftest reflected-path-reaches-a-fixture-even-when-the-ball-returns-to-its-start
  (let [settings (scene {:fast (assoc ball :radius 0.02 :position [1.48 2 0]
                                           :velocity [200 0 0])})
        rig [{:id :edge :position [1.95 2 0]}]
        start (spatial/advance nil settings {:time-ms 0} rig {})
        frame (spatial/advance (:state start) settings {:time-ms 5} rig {})
        hits (filter #(= :edge (:fixture-id %)) (:events frame))]
    (is (= #{} (get-in frame [:members :fast])))
    (is (= [:spatial/enter :spatial/exit :spatial/enter :spatial/exit] (mapv :type hits)))
    (is (every? true? (map near [2.25 2.45 2.55 2.75] (map :time-ms hits))))))

(deftest moving-a-volume-emits-only-changes-in-printed-fixture-order
  (let [groups [[-1 ["z-old" :left/a "a-old" :left/b]]
                [0 [:retained]]
                [1 [:right/b "a-new" :right/a "z-new"]]]
        fixtures (for [[x ids] groups id ids] {:id id :position [x 2 0]})
        step (fn [prior lo hi t]
               (let [box {:shape :box :min [lo 1 -1] :max [hi 3 1]}]
                 (spatial/advance (:state prior) (scene {:window box}) {:time-ms t :epoch 3} fixtures {})))
        before (step nil -2 0.5 0)
        moved (step before -0.5 2 25)
        changed (fn [type ids] (mapv (fn [id] {:type type :volume-id :window :fixture-id id :time-ms 25}) ids))]
    (is (= (into (changed :spatial/exit ["a-old" "z-old" :left/a :left/b])
                 (changed :spatial/enter ["a-new" "z-new" :right/a :right/b]))
           (:events moved)))
    (is (= #{:retained :right/b "a-new" :right/a "z-new"} (get-in moved [:members :window])))
    (is (empty? (:events (step moved -0.5 2 50))))))

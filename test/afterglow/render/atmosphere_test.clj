(ns afterglow.render.atmosphere-test
  (:require [afterglow.render.atmosphere :as fog]
            [afterglow.render.frame :as frame]
            [clojure.test :refer [deftest is]]))

(def fixture {:id :jet :position [1 2 3] :universe 4 :address 512 :channels {:fog [1 2]}
              :fogger {:flow-m3-min 60 :direction [0 0 -2] :mixing-seconds 4}})
(def room {:width 10 :height 4 :depth 5 :fog-half-life-s 60 :air-changes-per-hour 3})
(def plan (fog/plan room (frame/compile-patch [fixture])))
(def full {4 (assoc (vec (repeat 512 0)) 511 -1) 5 [0]})
(def off {4 (vec (repeat 512 0)) 5 [0]})
(defn near? [a b] (< (abs (- a b)) 1e-8))
(defn total [s] (+ (:mixed-m3 s) (reduce + 0 (map :local-m3 (:sources s)))))

(deftest split-universe-controls-hold-each-byte-independently
  (let [s (fog/initial plan 0 0)
        high {4 (assoc (vec (repeat 512 0)) 511 120)}
        send #(fog/present plan %1 %2 %3)
        a (send s 1000 high)
        b (send a 2000 {5 [128]})
        c (send b 3000 {4 (vec (repeat 512 0))})
        flow #(get-in % [:sources 0 :flow-m3-s])]
    (is (near? (/ 120 255) (flow a)))
    (is (near? (/ (+ 120 (/ 128 255)) 255) (flow b)))
    (is (near? (/ 128 (* 255 255)) (flow c)))
    (is (near? (+ (flow a) (flow b)) (get-in c [:sources 0 :emitted-m3])))
    (is (= (:sources c) (:sources (send c 3000 {6 [0]}))))))

(deftest flow-is-applied-to-the-correct-interval-and-diffuses-after-switch-off
  (let [s (fog/initial plan 2 0)
        on (fog/present plan s 500 full)
        mid (fog/present plan on 2500 full)
        stop (fog/present plan mid 4500 off)
        late (fog/advance plan stop 8500)
        once (fog/present plan on 4500 off)
        details (first (:sources late))]
    (is (zero? (total on)))
    (is (= [0.0 0.0 -1.0] (:direction details)))
    (is (= 4.0 (:emitted-m3 details)))
    (is (< 0 (total late) (total stop) 4))
    (is (< (:mixed-m3 stop) (:mixed-m3 late)))
    (is (near? (total stop) (total once)))
    (is (near? (get-in stop [:sources 0 :local-m3]) (get-in once [:sources 0 :local-m3])))
    (is (near? (/ (:mixed-m3 late) 200) (:mixed-density late)))
    (is (thrown? Exception (fog/advance plan late 8499)))
    (is (near? (total late) (total (fog/reconfigure (assoc plan :sources []) late 3 123 true))))))
(deftest partial-dmx-range-reversed-address-and-finite-fog-validation
  (let [plan (fog/plan room (frame/compile-patch [(assoc-in fixture [:fogger :dmx-range] [240 40])]))
        s (fog/initial plan 0 0)
        on (fog/present plan s 0 {4 (assoc (vec (repeat 512 0)) 511 140) 5 [0]})]
    (is (= 0.5 (get-in on [:sources 0 :flow-m3-s])))
    (is (= 0.5 (get-in (fog/present plan on 1000 {7 [0]}) [:sources 0 :flow-m3-s])))
    (is (thrown? Exception (fog/validate-fogger! (assoc-in fixture [:fogger :flow-m3-min] -1))))
    (is (thrown? Exception (fog/plan (assoc room :fog-half-life-s 0) (frame/compile-patch [fixture]))))))

(ns afterglow.render.gpu-session-test
  (:require [afterglow.render.gpu.expressions :as expressions]
            [afterglow.render.gpu.session :as session]
            [clojure.test :refer [deftest is]])
  (:import [java.util.concurrent CancellationException Future]))

(def spatial {:level {:op :add :args [{:op :position :axis :x} {:op :param :key :level}]}})
(def env {:params {:level 0.25}})
(defn- levels [result] (vec (get-in result [:outputs :level :values])))

(deftest groups-use-immutable-rig-keys-and-least-recently-used-eviction
  (let [mutable (double-array [0 0 0 1 0 0])
        first-group (session/group spatial mutable)
        equal-group (session/group spatial [[0.0 0.0 0.0] [1.0 0.0 0.0]])
        reordered (session/group spatial [[1 0 0] [0 0 0]])
        changed (session/group (assoc spatial :level {:op :const :value 0.5}) [[0 0 0] [1 0 0]])]
    (aset-double mutable 0 50)
    (is (= first-group equal-group))
    (with-open [owner (session/open! {:max-programs 2})]
      (let [old (session/evaluate! owner first-group env)]
        (is (= [0.25 1.25] (levels old)))
        (is (= [1.25 0.25] (levels (session/evaluate! owner reordered env))))
        (is (= [0.25 1.25] (levels (session/evaluate! owner equal-group env))))
        (is (= [0.5 0.5] (levels (session/evaluate! owner changed {}))))
        (is (= [1 3 1 2] ((juxt :hits :misses :evictions :resident) (session/status owner))))
        (is (false? (session/evict! owner reordered)))
        (is (true? (session/evict! owner first-group)))
        (is (= [0.25 1.25] (levels old)))))))

(deftest multiple-callers-use-one-owner-and-return-independent-arrays
  (with-open [owner (session/open! {:queue-capacity 16})]
    (let [g (session/group spatial [[1 2 3]])
          jobs (mapv #(future (session/evaluate! owner g {:params {:level %}})) (range 12))
          results (mapv deref jobs)]
      (is (= (mapv #(vector (+ 1.0 %)) (range 12)) (mapv levels results)))
      (is (= [1 11 1] ((juxt :resident :hits :misses) (session/status owner))))
      (aset-double ^doubles (get-in (first results) [:outputs :level :values]) 0 -9.0)
      (is (= [2.0] (levels (second results)))))))

(deftest admission-cancellation-and-timed-close-preserve-the-active-native-call
  (let [owner (session/open! {:queue-capacity 1})
        g (session/group spatial [[0 0 0]])
        running (promise) release (promise)
        run-native expressions/run-program!]
    (try
      (with-redefs [expressions/run-program!
                    (fn [& args]
                      (deliver running true)
                      (when (= ::timeout (deref release 10000 ::timeout)) (throw (ex-info "Test worker timed out" {})))
                      (apply run-native args))]
        (let [first-job (session/submit! owner g env)]
          (is (= true (deref running 5000 ::timeout)))
          (let [abandoned (session/submit! owner g env)]
            (is (.cancel ^Future abandoned true))
            (is (thrown? CancellationException (.get ^Future abandoned)))
            (is (zero? (:queued (session/status owner)))))
          (let [queued (session/submit! owner g env)]
            (is (= ::session/busy (try (session/submit! owner g env) nil
                                       (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))
            (is (false? (session/close! owner 5)))
            (is (thrown? CancellationException (.get ^Future queued)))
            (is (= ::session/closed (try (session/submit! owner g env) nil
                                         (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))
            (deliver release true)
            (is (= [0.25] (levels (.get ^Future first-job)))))))
      (is (true? (session/close! owner 5000)))
      (is (zero? (:resident (session/status owner))))
      (finally (deliver release true) (.close owner)))))

(deftest mutated-queued-environment-and-invalid-groups-preserve-good-programs
  (let [g (session/group spatial [[0 0 0]])
        reached (promise) release (promise) run-native expressions/run-program!]
    (with-open [owner (session/open! {:max-programs 1 :queue-capacity 2})]
      (try
        (with-redefs [expressions/run-program!
                      (fn [& args] (deliver reached true) (deref release 10000 false) (apply run-native args))]
          (let [first-job (session/submit! owner g env)]
            (is (= true (deref reached 5000 ::timeout)))
            (let [mutable (doto (java.util.HashMap.) (.put :level 0.75))
                  copied (session/submit! owner g {:params mutable})]
              (.put mutable :level 1.0)
              (deliver release true)
              (is (= [0.75] (levels (.get ^Future copied))))
              (is (= [0.25] (levels (.get ^Future first-job)))))))
        (finally (deliver release true)))
      ;; A compile failure is recoverable. Inject a bad emitted shader here to
      ;; exercise the driver failure and native object disposal, not the IR parser.
      (let [bad (assoc-in g [:plan :source] "#version 330 core\nvoid main(invalid){}")]
        (is (thrown? clojure.lang.ExceptionInfo (session/evaluate! owner bad env)))
        (is (= [0.25] (levels (session/evaluate! owner g env))))
        (is (= [1 0] ((juxt :resident :evictions) (session/status owner))))))))

(deftest equal-captured-uniforms-reuse-the-result-and-own-independent-readbacks
  (with-open [owner (session/open!)]
    (let [g (session/group spatial [[0 0 0]])
          result (session/evaluate! owner g env)]
      (aset-double ^doubles (get-in result [:outputs :level :values]) 0 0.9)
      (is (= [0.25] (levels (session/evaluate! owner g (assoc env :time-ms 15)))))
      (is (= 1 (:draws (session/status owner))))
      (is (= [0.75] (levels (session/evaluate! owner g {:params {:level 0.75}}))))
      (is (= 2 (:draws (session/status owner))))
      (session/evict! owner g)
      (is (= [0.75] (levels (session/evaluate! owner g {:params {:level 0.75}}))))
      (is (= 3 (:draws (session/status owner)))))))

(ns afterglow.runtime.executor-test
  (:require [afterglow.runtime.executor :as executor]
            [clojure.test :refer [deftest is]])
  (:import [java.util.concurrent CountDownLatch TimeUnit]))

(deftest bounded-pool-handles-more-jobs-than-its-queue
  (with-open [pool (executor/create {:workers 2 :queue-size 2 :timeout-ms 1000})]
    (is (= (mapv #(* % %) (range 50))
           (vec (sort (executor/map-work pool #(* % %) (range 50))))))))

(deftest worker-failure-is-reported-with-original-cause
  (let [cause (ex-info "Broken effect" {:effect-id "bad"})]
    (with-open [pool (executor/create {:workers 1 :queue-size 1 :timeout-ms 1000})]
      (try
        (executor/map-work pool (fn [_] (throw cause)) [1])
        (is false "Expected worker failure")
        (catch clojure.lang.ExceptionInfo e
          (is (= ::executor/worker-failed (:type (ex-data e))))
          (is (identical? cause (.getCause e)))))
      (is (= [2 3 4] (sort (executor/map-work pool inc [1 2 3])))))))

(deftest whole-frame-deadline-cancels-blocked-work
  (let [started (CountDownLatch. 1)
        blocked (CountDownLatch. 1)
        interrupted (CountDownLatch. 1)]
    (with-open [pool (executor/create {:workers 1 :queue-size 1 :timeout-ms 50})]
      (try
        (executor/map-work pool (fn [_]
                                  (.countDown started)
                                  (try (.await blocked)
                                       (catch InterruptedException e
                                         (.countDown interrupted)
                                         (throw e)))) [1])
        (is false "Expected deadline failure")
        (catch clojure.lang.ExceptionInfo e
          (is (= ::executor/timeout (:type (ex-data e))))))
      (is (.await started 1 TimeUnit/SECONDS))
      (is (.await interrupted 1 TimeUnit/SECONDS)))))

(deftest closed-pools-reject-new-work
  (let [pool (executor/create)]
    (executor/close! pool)
    (is (= ::executor/closed
           (try (executor/map-work pool identity [1])
                (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))))

(deftest concurrent-frame-submission-is-rejected-without-overlap
  (with-open [pool (executor/create {:timeout-ms 2000})]
    (let [started (promise) release (promise)
          first-frame (future (executor/map-work pool
                                                (fn [x] (deliver started true) @release x) [1]))]
      (try
        (is (= true (deref started 1000 :timeout)))
        (is (= ::executor/busy
               (try (executor/map-work pool identity [2])
                    (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))
        (deliver release true)
        (is (= [1] (deref first-frame 1000 :timeout)))
        (finally (deliver release true) (future-cancel first-frame))))))

(deftest invalid-pool-bounds-are-rejected
  (doseq [options [{:workers 0} {:queue-size 0} {:timeout-ms 0}
                   {:workers 1.5} {:timeout-ms Double/NaN}]]
    (is (thrown? clojure.lang.ExceptionInfo (executor/create options)))))

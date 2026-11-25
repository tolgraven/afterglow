(ns afterglow.control.codecs.osc-test
  (:require [clojure.test :refer [deftest is]]
            [afterglow.control.codecs.osc :as osc]))

(def envelope {:command-id "osc:9" :show-id :main :epoch 1
               :source {:adapter :osc :session-id "osc"} :time-ms 200})

(def mappings
  {"/cue/red" {:op :cue/launch :cue-id :red :launch {:mode :one-shot :duration-ms 500}}
   "/release" {:op :instance/end :instance-id "instance-4"}
   "/force" {:op :instance/end :instance-id "instance-4" :force? true}
   "/level" {:op :param/set :instance-id "instance-4" :param :level}
   "/master" {:op :master/set}
   "/blackout" {:op :blackout/set}})

(deftest osc-translates-through-explicit-mappings
  (is (= (merge envelope (get mappings "/cue/red"))
         (osc/command mappings {:path "/cue/red" :args []} envelope)))
  (is (= (merge envelope {:op :instance/end :instance-id "instance-4"})
         (osc/command mappings {:path "/release" :args []} envelope)))
  (is (= (merge envelope {:op :instance/end :instance-id "instance-4" :force? true})
         (osc/command mappings {:path "/force" :args []} envelope)))
  (is (= (merge envelope {:op :param/set :instance-id "instance-4" :param :level :value 0.75})
         (osc/command mappings {:path "/level" :args [0.75]} envelope)))
  (is (nil? (osc/command mappings {:path "/unknown" :args [1]} envelope))))

(deftest osc-does-not-permit-injected-operation-overrides
  (is (= :cue/launch (:op (osc/command mappings {:path "/cue/red" :args [] :op :show/restart}
                                       (assoc envelope :op :show/restart)))))
  (is (= "instance-4" (:instance-id (osc/command mappings {:path "/release" :args []}
                                                     (assoc envelope :instance-id "replacement"))))))

(deftest osc-translates-explicit-active-and-launch-priority-mappings
  (let [priority-mappings (assoc mappings
                                "/priority" {:op :instance/set-priority :instance-id "instance-4"}
                                "/cue/priority" {:op :cue/launch :cue-id :red :priority-arg? true
                                                  :launch {:mode :timed :duration-ms 500 :priority 9}})
        translate (fn [path args]
                    (osc/command priority-mappings {:path path :args args :instance-id "injected"} envelope))]
    (is (= (merge envelope {:op :instance/set-priority :instance-id "instance-4" :priority -2.5})
           (translate "/priority" [-2.5])))
    (is (= (merge envelope {:op :cue/launch :cue-id :red :launch {:mode :timed :duration-ms 500 :priority 4}})
           (translate "/cue/priority" [4])))
    (doseq [path ["/priority" "/cue/priority"]
            args [[] [2 3] ["2"] [nil] [Double/NaN] [Double/NEGATIVE_INFINITY]]]
      (is (thrown? clojure.lang.ExceptionInfo (translate path args))))))

(deftest boolean-buttons-and-normalized-master
  (doseq [[value expected] [[true true] [false false] [1 true] [0 false] [1.0 true] [0.0 false]]]
    (is (= expected (:value (osc/command mappings {:path "/blackout" :args [value]} envelope)))))
  (doseq [value [0 0.4 1]]
    (is (= value (:value (osc/command mappings {:path "/master" :args [value]} envelope)))))
  (doseq [value [-0.1 1.1 Double/NaN Double/POSITIVE_INFINITY "1"]]
    (is (thrown? clojure.lang.ExceptionInfo
                 (osc/command mappings {:path "/master" :args [value]} envelope)))))

(deftest malformed-osc-and-incomplete-envelopes-are-rejected
  (doseq [message [{:path "master" :args [1]}
                   {:path "/master" :args '(1)}
                   {:path "/master" :args []}
                   {:path "/cue/red" :args [1]}
                   {:path "/blackout" :args [0.5]}]]
    (is (thrown? clojure.lang.ExceptionInfo (osc/command mappings message envelope))))
  (doseq [key [:command-id :show-id :epoch :source :time-ms]]
    (is (thrown? clojure.lang.ExceptionInfo
                 (osc/command mappings {:path "/release" :args []} (dissoc envelope key)))))
  (is (thrown? clojure.lang.ExceptionInfo
               (osc/command {"/unknown" {:op :show/restart}} {:path "/unknown" :args []} envelope))))

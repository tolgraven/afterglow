(ns afterglow.web.access-test
  (:require [afterglow.core :as core]
            [afterglow.web.access :as access]
            [afterglow.web.handler :as web]
            [clojure.test :refer [deftest is]])
  (:import [java.nio.charset StandardCharsets]
           [java.util Base64]))

(defn- request [peer host]
  {:request-method :get :uri "/" :remote-addr peer :headers {"host" host}})

(deftest local-operator-requires-local-peer-and-authority
  (let [app (access/wrap-operator (constantly {:status 200}) {})]
    (doseq [[peer host] [["127.0.0.1" "localhost:16000"] ["::1" "[::1]:16000"]]]
      (is (= 200 (:status (app (request peer host))))))
    (doseq [r [(request "192.0.2.10" "localhost") (request "127.0.0.1" "desk.example")
               (request "127.0.0.1" nil) (request "127.0.0.1" "localhost/path")
               (assoc-in (request "192.0.2.10" "localhost") [:headers "x-forwarded-for"] "127.0.0.1")
               (assoc-in (request "127.0.0.1" "localhost") [:headers "x-forwarded-for"] "127.0.0.1")]]
      (is (= 403 (:status (app r)))))))

(deftest lan-operator-needs-explicit-authentication-even-for-loopback-peers
  (is (thrown? clojure.lang.ExceptionInfo (access/wrap-operator identity {:bind "0.0.0.0"})))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"requires AFTERGLOW_WEB_TOKEN"
                        (core/start-web-server 16000 false {:bind "0.0.0.0"})))
  (let [app (access/wrap-operator (fn [r] {:status (if (contains? (:headers r) "authorization") 500 204)})
                                  {:bind "0.0.0.0" :token "operator-test"})
        credentials (str "Basic " (.encodeToString (Base64/getEncoder)
                                                   (.getBytes "afterglow:operator-test" StandardCharsets/UTF_8)))]
    (doseq [r [(request "192.0.2.5" "desk.local") (request "127.0.0.1" "localhost")]]
      (is (= 401 (:status (app r))))
      (is (= 401 (:status (app (assoc-in r [:headers "authorization"] "Basic invalid")))))
      (is (= 204 (:status (app (assoc-in r [:headers "authorization"] credentials))))))))


(deftest embedded-routes-check-operator-access-before-parsing-console-input
  (let [remote (assoc (request "192.0.2.10" "localhost") :uri "/console" :request-method :post)
        protected (web/application {:bind "0.0.0.0" :token "operator-test"})]
    (is (= 403 (:status (web/app remote))))
    (is (= 401 (:status (protected remote))))
    (is (= 200 (:status (web/app (assoc (request "127.0.0.1" "localhost:16000")
                                       :uri "/about" :scheme :http)))))))

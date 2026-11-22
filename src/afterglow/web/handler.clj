(ns afterglow.web.handler
  (:require [afterglow.web.access :as access]
            [afterglow.web.middleware :as middleware]
            [afterglow.web.routes.home :refer [home-routes]]
            [compojure.core :refer [defroutes routes wrap-routes]]
            [compojure.route :as route]))

(defroutes base-routes
           (route/resources "/")
           (route/not-found "Not Found"))

(def ^:private routes-app
  (-> (routes
        (wrap-routes home-routes middleware/wrap-csrf)
        base-routes)
      middleware/wrap-base))


(defn application [options]
  (access/wrap-operator routes-app options))

(def app (application {}))

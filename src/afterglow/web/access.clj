(ns afterglow.web.access
  "Access to the embedded operator UI, which includes a full JVM REPL."
  (:require [clojure.string :as str])
  (:import [java.net URI]
           [java.nio.charset StandardCharsets]
           [java.security MessageDigest]
           [java.util Base64]))

(def loopback-bind "127.0.0.1")

(defn- loopback? [address]
  (contains? #{"127.0.0.1" "::1" "[::1]" "0:0:0:0:0:0:0:1" "[0:0:0:0:0:0:0:1]" "localhost"}
             (some-> address str/lower-case)))

(defn- local-authority? [authority]
  (when (string? authority)
    (try
      (let [uri (URI. (str "http://" authority))]
        (and (= authority (.getRawAuthority uri))
             (nil? (.getUserInfo uri))
             (loopback? (.getHost uri))))
      (catch java.net.URISyntaxException _ false))))

(defn- digest [^String value]
  (.digest (MessageDigest/getInstance "SHA-256") (.getBytes value StandardCharsets/UTF_8)))

(defn wrap-operator
  "Loopback requires both a local socket peer and browser authority. Any other
  bind needs an operator password. Configuring a password protects local access
  too, including requests passing through a reverse proxy on the same machine."
  [handler {:keys [bind token] :or {bind loopback-bind}}]
  (when (and (not (loopback? bind)) (str/blank? token))
    (throw (ex-info "A LAN web binding requires AFTERGLOW_WEB_TOKEN" {:bind bind})))
  (if (str/blank? token)
    (fn [request]
      ;; HTTP Kit's Ring remote-addr may be derived from X-Forwarded-For.
      ;; Token-free access therefore permits only unforwarded requests.
      (if (and (not (contains? (:headers request) "x-forwarded-for"))
               (loopback? (:remote-addr request))
               (local-authority? (get-in request [:headers "host"])))
        (handler request)
        {:status 403 :headers {"Cache-Control" "no-store"} :body "Local operator access required"}))
    (let [credential (str "Basic " (.encodeToString (Base64/getEncoder)
                                                    (.getBytes (str "afterglow:" token) StandardCharsets/UTF_8)))
          expected (digest credential)]
      (fn [request]
        (let [supplied (get-in request [:headers "authorization"])]
          (if (and (string? supplied) (MessageDigest/isEqual expected (digest supplied)))
            (handler (update request :headers dissoc "authorization"))
            {:status 401 :body "Operator authentication required"
             :headers {"Cache-Control" "no-store" "WWW-Authenticate" "Basic realm=\"Afterglow\", charset=\"UTF-8\""}}))))))

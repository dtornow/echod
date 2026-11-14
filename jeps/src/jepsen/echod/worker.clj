(ns jepsen.echod.worker
  "The address a node pushes to. echod has no poll API: after a commit it
  POSTs `execute` and `unblock` here. The checker reads what arrived. The
  server is on the control node, which for a local run is the same machine
  as the nodes."
  (:require [cheshire.core :as json]
            [clojure.tools.logging :refer [info]])
  (:import (com.sun.net.httpserver HttpExchange HttpHandler HttpServer)
           (java.net InetSocketAddress)))

(defonce server (atom nil))
(defonce advertised (atom nil))
(defonce inbox (atom []))

(defn url
  []
  @advertised)

(defn reset-inbox!
  []
  (reset! inbox []))

(defn messages
  []
  @inbox)

(defn unblocks
  "One map per unblock push: :id and :state of the promise it carried."
  []
  (for [m @inbox
        :let [msg (:msg m)]
        :when (= "unblock" (get msg "kind"))]
    {:id (get-in msg ["data" "promise" "id"])
     :state (get-in msg ["data" "promise" "state"])
     :at (:at m)}))

(defn executes
  []
  (for [m @inbox
        :let [msg (:msg m)]
        :when (= "execute" (get msg "kind"))]
    {:id (get-in msg ["data" "task" "id"])
     :version (get-in msg ["data" "task" "version"])
     :at (:at m)}))

(defn- handler
  []
  (reify HttpHandler
    (^void handle [_ ^HttpExchange ex]
      (try
        (let [text (slurp (.getRequestBody ex))
              msg (try (json/parse-string text)
                       (catch Exception _ {:unparsed text}))]
          (swap! inbox conj {:at (System/currentTimeMillis) :msg msg})
          (.sendResponseHeaders ex 200 -1))
        (catch Exception e
          (info e "worker failed a push")
          (try (.sendResponseHeaders ex 500 -1) (catch Exception _ nil)))
        (finally
          (.close ex)))
      nil)))

(defn ensure-started!
  "Bind every interface on an ephemeral port, once, and advertise `host`.
  Local runs advertise 127.0.0.1. A remote cluster must pass a host its
  nodes can route to. Idempotent; the first host wins until `stop!`."
  [host]
  (locking server
    (when-not @server
      (let [s (HttpServer/create (InetSocketAddress. "0.0.0.0" 0) 0)]
        (.createContext s "/" (handler))
        (.setExecutor s nil)
        (.start s)
        (let [port (.getPort (.getAddress s))
              u (str "http://" host ":" port "/")]
          (reset! server s)
          (reset! advertised u)
          (info "push worker listening on" u)
          u)))))

(defn stop!
  []
  (locking server
    (when-let [s @server]
      (.stop s 0)
      (reset! server nil)
      (reset! advertised nil))))

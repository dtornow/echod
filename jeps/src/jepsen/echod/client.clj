(ns jepsen.echod.client
  "A client that only speaks HTTP. Nothing here calls into the process, the
  store, or the simulator: if a history passes, it passed from the outside.

  Definite answers — 200, 404, 409, and any other status the envelope
  carries — are `:ok`. The model decides whether that answer was legal.
  503, a timeout, and a socket error are `:info`: the call may have
  committed. A final read retries those, so a node that is still coming
  back from a restart can still close the history."
  (:require [cheshire.core :as json]
            [clojure.string :as str]
            [clojure.tools.logging :refer [info]]
            [jepsen.client :as client]
            [jepsen.echod.core :as c]
            [jepsen.echod.wire :as wire]
            [jepsen.echod.worker :as worker]
            [jepsen.independent :as ind])
  (:import (java.net URI)
           (java.net.http HttpClient HttpRequest HttpRequest$BodyPublishers
                          HttpResponse$BodyHandlers)
           (java.time Duration)))

(defn http-client
  [timeout-ms]
  (-> (HttpClient/newBuilder)
      (.connectTimeout (Duration/ofMillis timeout-ms))
      .build))

(defn post-raw
  "POST `body` to `url`. Returns `{:http :headers :text}` or throws."
  [^HttpClient http url body timeout-ms]
  (let [req (-> (HttpRequest/newBuilder)
                (.uri (URI/create url))
                (.timeout (Duration/ofMillis timeout-ms))
                (.header "content-type" "application/json")
                (.POST (HttpRequest$BodyPublishers/ofString body))
                .build)
        resp (.send http req (HttpResponse$BodyHandlers/ofString))
        headers (into {} (for [[k vs] (.map (.headers resp))]
                           [(str/lower-case (str k)) (first vs)]))]
    {:http (.statusCode resp)
     :headers headers
     :text (.body resp)}))

(defn interpret
  "The request map plus the parsed response, or an `{:info :error}` map
  when the call did not produce an envelope."
  [request raw]
  (try
    (let [parsed (json/parse-string (:text raw))]
      (if (map? parsed)
        (wire/parse-response request (:http raw) (:headers raw) parsed)
        {:info true :error :unreadable}))
    (catch Exception e
      {:info true :error (str "unreadable response: " (.getMessage e))})))

(defn call-budget
  "How long one attempt may take, and how many attempts a call gets.
  A final read retries: the node may still be coming back from a restart."
  [test op]
  (let [v (:value op)
        inner (if (ind/tuple? v) (val v) v)]
    (if (:final? inner)
      {:ms (long (:final-timeout test 10000)) :attempts 8}
      {:ms (long (:timeout test 5000)) :attempts 1})))

(defn classify
  "503 did not produce an answer. Every other status is the envelope, and
  the model decides whether that answer was legal."
  [http-status]
  (if (= 503 http-status) :info :ok))

(defn- note-version!
  "The highest task version a response showed us. The generator reads this
  when it builds the next acquire; a stale guess is a legal 409."
  [versions k response]
  (when (and versions k (:task response) (:version (:task response)))
    (swap! versions update k (fnil max 0) (long (:version (:task response))))))

(defn perform
  "One attempt, or several when this is a final read."
  [http url timeout-ms attempts op address versions]
  (let [v (:value op)
        [k inner] (if (ind/tuple? v) [(key v) (val v)] [nil v])
        payload (wire/encode (assoc op :value inner) address)]
    (if (nil? payload)
      (assoc op :type :fail :error :not-a-request)
      (loop [attempt 0]
        (let [outcome (try
                        (let [raw (post-raw http url payload timeout-ms)
                              parsed (interpret inner raw)]
                          (if (:info parsed)
                            {:kind :info :error (:error parsed)}
                            {:kind (classify (:http parsed))
                             :error (when (= 503 (:http parsed)) :unavailable)
                             :value parsed}))
                        (catch Exception e
                          {:kind :info :error (.getMessage e)}))]
          (cond
            (and (= :info (:kind outcome)) (< (inc attempt) attempts))
            (do (Thread/sleep 250) (recur (inc attempt)))

            (= :ok (:kind outcome))
            (do (note-version! versions k (:value outcome))
                (assoc op :type :ok
                       :value (if (some? k)
                                (ind/tuple k (:value outcome))
                                (:value outcome))))

            :else
            (assoc op :type :info :error (:error outcome))))))))

(defrecord EchodClient [http timeout final-timeout versions nodes all?]
  client/Client
  (open! [this test node]
    (let [budget-ms (max (long (:timeout test 5000))
                         (long (:final-timeout test 10000)))]
      (assoc this
             :nodes (vec (:nodes test))
             :all? (= :all (:client-nodes test :all))
             :timeout (long (:timeout test 5000))
             :final-timeout (long (:final-timeout test 10000))
             :http (or http (http-client budget-ms))
             :pinned node)))

  (setup! [this _test] this)

  (invoke! [this test op]
    (let [node (if all? (rand-nth nodes) (:pinned this))
          url (c/node-url test node)
          address (worker/url)
          {:keys [ms attempts]} (call-budget test op)]
      (perform http url ms attempts op address versions)))

  (close! [this _test]
    (when http
      (try (.close http) (catch Exception _)))
    this)

  (teardown! [this _test] this)

  client/Reusable
  (reusable? [_ _] true))

(defn client
  "A reusable HTTP client. `versions` is an atom of key -> task version
  the generator and the client share; nil when the workload has no tasks."
  [versions]
  (map->EchodClient {:versions versions}))

(ns jepsen.echod.core
  "Ids, URLs, and the small pure helpers the rest of the suite shares.

  A promise id is `o<origin>:p<key>`. `:share` keys share an origin, so they
  share one document and one conditional writer. The checker still treats
  each promise as its own state machine: a lost update that clobbers a
  neighbour shows up as that neighbour's history failing to linearize."
  (:require [clojure.string :as str]))

(def settable-states
  "States a client may settle a promise to."
  #{"resolved" "rejected" "rejected_canceled"})

(def promise-states
  (conj settable-states "pending" "rejected_timedout"))

(defn n
  "A JSON number as a long, or nil."
  [x]
  (when (number? x) (long x)))

(defn promise-id
  "The server id of key `k`. Keys `share` apart live in one origin."
  [opts k]
  (let [share (long (:share opts 4))
        k (long k)]
    (str "o" (quot k share) ":p" k)))

(defn schedule-id
  [k]
  (str "sched-" k))

(defn node-port
  "Local listen port for `node`. Remote nodes all use `:port`."
  [test node]
  (if (:local? test)
    (let [i (.indexOf ^java.util.List (vec (:nodes test)) node)]
      (+ (long (:base-port test 18001)) (max 0 i)))
    (long (:port test 8001))))

(defn node-url
  "The URL a client uses for `node`, with a trailing slash."
  [test node]
  (if (:local? test)
    (str "http://127.0.0.1:" (node-port test node) "/")
    (str "http://" node ":" (node-port test node) "/")))

(defn tags
  "Tags as a sorted map of strings, so comparison ignores JSON order."
  [m]
  (into (sorted-map)
        (for [[k v] (or m {})]
          [(str k) (str v)])))

(defn request-tags
  "The tags a create actually sends. An empty set is the global scope: a
  promise with no tags is not awaitable, and a listener on it is a 422."
  [v]
  (let [t (:tags v)]
    (tags (if (empty? t) {"resonate:scope" "global"} t))))

(defn targeted?
  "A create with `resonate:target` is born with a task at version 0."
  [v]
  (or (:target? v)
      (contains? (tags (:tags v)) "resonate:target")))

(defn timer?
  [v]
  (= "true" (get (tags (:tags v)) "resonate:timer")))

(defn value-of
  "The operation's payload. Independent histories arrive already unwrapped;
  a MapEntry or a `[k v]` pair is unwrapped here too, so a checker can be
  called either way."
  [op]
  (let [v (:value op)]
    (cond
      (map-entry? v) (val v)
      (and (vector? v) (= 2 (count v)) (map? (second v))) (second v)
      :else v)))

(defn key-of
  [op]
  (let [v (:value op)]
    (cond
      (map-entry? v) (key v)
      (and (vector? v) (= 2 (count v)) (map? (second v))) (first v)
      :else nil)))

(defn observed?
  "An `:ok` completion carries the server's status. An `:info` op carries
  only the request, which is what Knossos steps when it assumes the call
  landed."
  [v]
  (and (map? v) (contains? v :status)))

(defn blank?
  [s]
  (or (nil? s) (not (string? s)) (str/blank? s)))

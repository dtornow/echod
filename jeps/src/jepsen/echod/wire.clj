(ns jepsen.echod.wire
  "The Resonate envelope, and the records we keep from a response.

  The node speaks one POST `/`. A response whose HTTP status is not the
  envelope's `head.status` is already a broken pipeline; the model rejects
  it. Error bodies are a string. Success bodies carry the record."
  (:require [cheshire.core :as json]
            [clojure.string :as str]
            [jepsen.echod.core :as c]))

(def protocol-version "2026-04-01")

(defn envelope
  "A request envelope. `data` is the kind's object."
  [kind data]
  {:kind kind
   :head {:corrId (str (random-uuid))
          :version protocol-version}
   :data data})

(defn value-data
  "A promise value. Nil data is the empty value the server stores for a
  create, and for a settle that names none."
  [data]
  (if (some? data) {:data data} {}))

(defn create-data
  [v]
  {:id (:id v)
   :timeoutAt (c/n (:timeout-at v))
   :param (value-data (:param v))
   :tags (c/request-tags v)})

(defn settle-data
  [v]
  {:id (:id v)
   :state (:state v)
   :value (value-data (:value v))})

(defn fulfill-data
  "task.fulfill's action is a promise.settle of the task's own promise."
  [v]
  {:id (:id v)
   :version (c/n (:version v))
   :action {:kind "promise.settle"
            :head {}
            :data (settle-data v)}})

(defn acquire-data
  [v]
  {:id (:id v)
   :version (c/n (:version v))
   :pid (:pid v)
   :ttl (c/n (:ttl v))})

(defn release-data
  [v]
  {:id (:id v)
   :version (c/n (:version v))})

(defn heartbeat-data
  [v]
  {:pid (:pid v)
   :tasks [{:id (:id v) :version (c/n (:version v))}]})

(defn listen-data
  [v address]
  {:awaited (:id v)
   :address address})

(defn schedule-create-data
  [v]
  {:id (:id v)
   :cron (:cron v)
   :promiseId (:promise-id v)
   :promiseTimeout (c/n (:promise-timeout v))
   :promiseParam (value-data (:param v))
   :promiseTags (c/request-tags v)})

(defn id-data
  [v]
  {:id (:id v)})

(defn body
  "kind and data for an operation, or nil if this op is not a request
  (a nemesis op, a log line)."
  [op address]
  (let [v (c/value-of op)]
    (let [schedule? (or (:schedule? v) (:cron v))]
      (case (:f op)
      :create (if schedule?
                ["schedule.create" (schedule-create-data v)]
                ["promise.create" (create-data v)])
      :get (if schedule?
             ["schedule.get" (id-data v)]
             ["promise.get" (id-data v)])
      :delete ["schedule.delete" (id-data v)]
      :settle ["promise.settle" (settle-data v)]
      :listen ["promise.register_listener" (listen-data v address)]
      :acquire ["task.acquire" (acquire-data v)]
      :release ["task.release" (release-data v)]
      :fulfill ["task.fulfill" (fulfill-data v)]
      :heartbeat ["task.heartbeat" (heartbeat-data v)]
      :task-get ["task.get" (id-data v)]
      nil))))

(defn encode
  [op address]
  (when-let [[kind data] (body op address)]
    (json/generate-string (envelope kind data))))

(defn- pick
  [m & ks]
  (some #(when (and (map? m) (contains? m %)) (get m %)) ks))

(defn parse-promise
  "The promise record the model compares. Field names are whatever the
  codec emits; both casings are accepted."
  [p]
  (when (map? p)
    {:id (get p "id")
     :state (get p "state")
     :param (get-in p ["param" "data"])
     :value (get-in p ["value" "data"])
     :timeout-at (c/n (pick p "timeoutAt" "timeout_at"))
     :tags (c/tags (get p "tags"))
     :created-at (c/n (pick p "createdAt" "created_at"))
     :settled-at (c/n (pick p "settledAt" "settled_at"))}))

(defn parse-task
  [t]
  (when (map? t)
    (let [pid (get t "pid")]
      {:id (get t "id")
       :state (get t "state")
       :version (c/n (get t "version"))
       :pid (when-not (c/blank? pid) pid)})))

(defn parse-schedule
  [s]
  (when (map? s)
    {:id (get s "id")
     :cron (get s "cron")
     :promise-id (pick s "promiseId" "promise_id")
     :promise-timeout (c/n (pick s "promiseTimeout" "promise_timeout"))
     :param (get-in s ["promiseParam" "data"])
     :tags (c/tags (pick s "promiseTags" "promise_tags"))
     :next-run-at (c/n (pick s "nextRunAt" "next_run_at"))
     :last-run-at (c/n (pick s "lastRunAt" "last_run_at"))
     :created-at (c/n (pick s "createdAt" "created_at"))}))

(defn parse-response
  "An HTTP response into the map the model sees, merged over the request.
  `:status` is the envelope. `:http` is the status line. They are the
  pipeline's two copies of one answer and must agree."
  [request http-status headers json-body]
  (let [data (get json-body "data")
        status (c/n (get-in json-body ["head" "status"]))
        node (some (fn [[k v]]
                     (when (= "x-echod-node" (str/lower-case (str k))) v))
                   headers)]
    (merge request
           {:http (c/n http-status)
            :status (or status (c/n http-status))
            :node node
            :kind (get json-body "kind")
            :promise (when (map? data) (parse-promise (get data "promise")))
            :task (when (map? data) (parse-task (get data "task")))
            :schedule (when (map? data) (parse-schedule (get data "schedule")))
            :error (when (string? data) data)})))

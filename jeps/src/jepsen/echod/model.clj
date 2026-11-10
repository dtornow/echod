(ns jepsen.echod.model
  "The document machine, as a client can see it.

  One promise is one state machine. `create` is idempotent: the first
  request to land names the promise, and every later create returns that
  promise untouched. `settle` writes a terminal state once; a settle that
  arrives after the promise has left `:pending` — because it was settled,
  or because this model is not asked to invent a timeout — returns the
  promise as it stands. A task is born at version 0 when the create carries
  `resonate:target`. `acquire` bumps that version. `release` drops the lease
  and keeps the version. `fulfill` and a client `settle` both settle the
  promise and fulfill the task. `heartbeat` is a lease extension the record
  does not show, so it is a legal no-op on the observable state.

  Knossos steps an `:ok` op with the server's answer (the request merged
  with `:status`, `:promise`, `:task`). It steps an `:info` op with the
  request alone, and also tries not stepping it. An `:info` step is the
  effect the call would have had if it landed: a create of a missing
  promise installs it, a create of an existing one does nothing, a settle
  of a pending promise settles it, an acquire whose version matches
  acquires it, and a call the machine would have rejected changes nothing.

  Timeouts are not a transition here. The promise workload arms deadlines
  an hour out, so a `rejected_timedout` read is a bug. The deadline
  workload checks that transition itself.

  A schedule is a second machine: create is idempotent, delete of a missing
  schedule is 404, and a schedule that fires (`lastRunAt` set) is rejected.
  The workload's cron is yearly, so a fire during the test is a bug or a
  clock jump."
  (:refer-clojure :exclude [promise])
  (:require [jepsen.echod.core :as c]
            [knossos.model :as model])
  (:import (knossos.model Model)))

(defn- bad
  [op msg]
  (model/inconsistent (str (:f op) ": " msg)))

(defn- envelope-ok
  "HTTP status and `head.status` are one answer written twice. The header
  `x-echod-node` is the gateway saying which process produced it."
  [op v]
  (cond
    (not= (:http v) (:status v))
    (bad op (str "HTTP " (:http v) " is not the envelope status " (:status v)))

    (c/blank? (:node v))
    (bad op "response has no x-echod-node header")

    :else nil))

;; ---------------------------------------------------------------------------
;; promises and tasks
;; ---------------------------------------------------------------------------

(defn- fresh-task
  []
  {:state "pending" :version 0 :pid nil})

(defn- fulfill-task
  [t]
  (when t
    (if (= "fulfilled" (:state t))
      t
      {:state "fulfilled" :version (:version t) :pid nil})))

(defn- same-promise
  "Does `seen` describe `have`? A created-at or settled-at we have not
  learned yet (an `:info` create) accepts the first number a read shows."
  [have seen]
  (and have seen
       (= (:state have) (:state seen))
       (= (:param have) (:param seen))
       (= (:value have) (:value seen))
       (= (c/n (:timeout-at have)) (c/n (:timeout-at seen)))
       (= (c/tags (:tags have)) (c/tags (:tags seen)))
       (number? (:created-at seen))
       (or (nil? (:created-at have))
           (= (c/n (:created-at have)) (c/n (:created-at seen))))
       (if (= "pending" (:state have))
         (nil? (:settled-at seen))
         (and (number? (:settled-at seen))
              (or (nil? (:settled-at have))
                  (= (c/n (:settled-at have)) (c/n (:settled-at seen))))))))

(defn- learn
  "Remember the timestamps a read just showed us."
  [p seen]
  (assoc p
         :created-at (c/n (:created-at seen))
         :settled-at (c/n (:settled-at seen))
         :tags (c/tags (:tags seen))))

(defn- observe
  [op m seen]
  (let [p (:p m)]
    (cond
      (nil? p) (bad op (str "read " (:state seen) " of a promise that does not exist"))
      (not= (:id seen) (:id (:value op))) (bad op (str "promise id " (:id seen) " is not " (:id (:value op))))
      (not (same-promise p seen)) (bad op (str "saw " (pr-str seen) " but the promise is " (pr-str p)))
      :else (assoc m :p (learn p seen)))))

(defn- install-promise
  [v task created-at settled-at]
  {:param (:param v)
   :timeout-at (c/n (:timeout-at v))
   :tags (c/request-tags v)
   :state "pending"
   :value nil
   :created-at created-at
   :settled-at settled-at
   :task task})

(defn- install-from-response
  [op v]
  (let [pr (:promise v)]
    (cond
      (not= 200 (:status v)) (bad op (str "create status " (:status v)))
      (nil? pr) (bad op "create 200 without a promise")
      (not= "pending" (:state pr)) (bad op (str "a new promise was born " (:state pr)))
      (not= (:param v) (:param pr)) (bad op (str "create stored param " (pr-str (:param pr)) " not " (pr-str (:param v))))
      (not= (c/n (:timeout-at v)) (c/n (:timeout-at pr))) (bad op "create stored a different timeout")
      (not= (c/request-tags v) (c/tags (:tags pr))) (bad op (str "create stored tags " (pr-str (:tags pr))))
      (not (number? (:created-at pr))) (bad op "create returned no created-at")
      (some? (:settled-at pr)) (bad op "a pending promise has settled-at")
      :else {:p (install-promise pr
                                 (when (c/targeted? v) (fresh-task))
                                 (c/n (:created-at pr))
                                 nil)})))

(defn- install-from-request
  [v]
  {:p (install-promise v
                       (when (c/targeted? v) (fresh-task))
                       nil
                       nil)})

(defn- settle-into
  [p v]
  (assoc p
         :state (:state v)
         :value (:value v)
         :settled-at nil
         :task (fulfill-task (:task p))))

(defn- can-acquire?
  [p v]
  (let [t (:task p)]
    (and p t
         (= "pending" (:state p))
         (= "pending" (:state t))
         (= (c/n (:version t)) (c/n (:version v))))))

(defn- held?
  [p v]
  (let [t (:task p)]
    (and p t
         (= "pending" (:state p))
         (= "acquired" (:state t))
         (= (c/n (:version t)) (c/n (:version v))))))

(defn- task-missing?
  [p]
  (or (nil? p) (nil? (:task p))))

(defn- do-acquire
  [p v]
  (assoc p :task {:state "acquired"
                  :version (inc (c/n (:version (:task p))))
                  :pid (:pid v)}))

(defn- do-release
  [p]
  (assoc p :task {:state "pending"
                  :version (:version (:task p))
                  :pid nil}))

(defn- same-task
  [have seen]
  (and seen
       (= (:state have) (:state seen))
       (= (c/n (:version have)) (c/n (:version seen)))
       (= (:pid have) (:pid seen))))

(defn- check-task
  [op task seen]
  (cond
    (nil? seen) (bad op "200 without a task")
    (not (same-task task seen)) (bad op (str "task " (pr-str seen) " is not " (pr-str task)))
    :else nil))

(defn- step-create
  [op m v]
  (cond
    (not (c/observed? v))
    (if (:p m) m (assoc m :p (:p (install-from-request v))))

    (:p m)
    (if (not= 200 (:status v))
      (bad op (str "create of an existing promise returned " (:status v)))
      (observe op m (:promise v)))

    :else
    (let [installed (install-from-response op v)]
      (if (model/inconsistent? installed)
        installed
        (assoc m :p (:p installed))))))

(defn- step-read
  "get and register_listener both return the promise and leave it. The
  listener list is not part of the record."
  [op m v]
  (cond
    (not (c/observed? v)) m
    (= 404 (:status v)) (if (:p m) (bad op "404 for a promise that exists") m)
    (= 200 (:status v)) (observe op m (:promise v))
    :else (bad op (str "status " (:status v)))))

(defn- step-settle
  [op m v]
  (cond
    (not (c/settable-states (:state v)))
    (bad op (str "settle to " (:state v)))

    (not (c/observed? v))
    (let [p (:p m)]
      (cond
        (nil? p) m
        (not= "pending" (:state p)) m
        :else (assoc m :p (settle-into p v))))

    (= 404 (:status v))
    (if (:p m) (bad op "settle 404 for a promise that exists") m)

    (= 200 (:status v))
    (let [p (:p m)]
      (cond
        (nil? p) (bad op "settle 200 of a promise that does not exist")
        (= "pending" (:state p))
        (observe op (assoc m :p (settle-into p v)) (:promise v))
        :else
        (observe op m (:promise v))))

    :else (bad op (str "settle status " (:status v)))))

(defn- step-task-get
  [op m v]
  (cond
    (not (c/observed? v)) m
    (= 404 (:status v))
    (if (task-missing? (:p m)) m (bad op "task.get 404 but a task exists"))
    (= 200 (:status v))
    (cond
      (task-missing? (:p m)) (bad op "task.get 200 but no task exists")
      :else (or (check-task op (:task (:p m)) (:task v)) m))
    :else (bad op (str "task.get status " (:status v)))))

(defn- step-acquire
  [op m v]
  (let [p (:p m)
        ok-acquire (can-acquire? p v)]
    (cond
      (not (c/observed? v))
      (if ok-acquire (assoc m :p (do-acquire p v)) m)

      (= 200 (:status v))
      (cond
        (not ok-acquire) (bad op "acquire 200 but the task was not pending at that version")
        :else
        (let [p' (do-acquire p v)
              task-bad (check-task op (:task p') (:task v))
              m' (observe op (assoc m :p p') (:promise v))]
          (or task-bad m')))

      (= 409 (:status v))
      (if ok-acquire
        (bad op "acquire 409 but the task was pending at that version")
        (if (task-missing? p)
          (bad op "acquire 409 but there is no task; that is a 404")
          m))

      (= 404 (:status v))
      (if (task-missing? p) m (bad op "acquire 404 but a task exists"))

      :else (bad op (str "acquire status " (:status v))))))

(defn- step-release
  [op m v]
  (let [p (:p m)
        ok-release (held? p v)]
    (cond
      (not (c/observed? v))
      (if ok-release (assoc m :p (do-release p)) m)

      (= 200 (:status v))
      (if ok-release
        (assoc m :p (do-release p))
        (bad op "release 200 but the task was not acquired at that version"))

      (= 409 (:status v))
      (cond
        ok-release (bad op "release 409 but the lease was held")
        (task-missing? p) (bad op "release 409 but there is no task; that is a 404")
        :else m)

      (= 404 (:status v))
      (if (task-missing? p) m (bad op "release 404 but a task exists"))

      :else (bad op (str "release status " (:status v))))))

(defn- step-fulfill
  [op m v]
  (let [p (:p m)
        ok-fulfill (held? p v)]
    (cond
      (not (c/settable-states (:state v)))
      (bad op (str "fulfill to " (:state v)))

      (not (c/observed? v))
      (if ok-fulfill (assoc m :p (settle-into p v)) m)

      (= 200 (:status v))
      (if ok-fulfill
        (observe op (assoc m :p (settle-into p v)) (:promise v))
        (bad op "fulfill 200 but the lease was not held at that version"))

      (= 409 (:status v))
      (cond
        ok-fulfill (bad op "fulfill 409 but the lease was held")
        (task-missing? p) (bad op "fulfill 409 but there is no task; that is a 404")
        :else m)

      (= 404 (:status v))
      (if (task-missing? p) m (bad op "fulfill 404 but a task exists"))

      :else (bad op (str "fulfill status " (:status v))))))

(defn- step-heartbeat
  "A heartbeat extends a lease the record does not expose, and the server
  answers 200 even when nothing matched. It cannot change the promise."
  [op m v]
  (cond
    (not (c/observed? v)) m
    (= 200 (:status v)) m
    :else (bad op (str "heartbeat status " (:status v)))))

(defrecord PromiseModel [p]
  Model
  (step [this op]
    (let [v (:value op)
          env (when (c/observed? v) (envelope-ok op v))]
      (or env
          (case (:f op)
            :create (step-create op this v)
            (:get :listen) (step-read op this v)
            :settle (step-settle op this v)
            :task-get (step-task-get op this v)
            :acquire (step-acquire op this v)
            :release (step-release op this v)
            :fulfill (step-fulfill op this v)
            :heartbeat (step-heartbeat op this v)
            this))))

  Object
  (toString [_] (pr-str p)))

(defn promise
  "The empty document. Nothing has been created."
  []
  (PromiseModel. nil))

;; ---------------------------------------------------------------------------
;; schedules
;; ---------------------------------------------------------------------------

(defn- sched-client
  "The fields the client chose. `next-run-at` and `created-at` belong to
  the server."
  [v]
  {:cron (:cron v)
   :promise-id (:promise-id v)
   :promise-timeout (c/n (:promise-timeout v))
   :param (:param v)
   :tags (c/request-tags v)})

(defn- same-sched-client
  [have seen]
  (= (sched-client have) (sched-client seen)))

(defn- observe-schedule
  [op m seen]
  (let [s (:s m)]
    (cond
      (nil? s) (bad op "read a schedule that does not exist")
      (some? (:last-run-at seen)) (bad op "schedule fired; the strict schedule model forbids it")
      (not (number? (:next-run-at seen))) (bad op "schedule has no next-run-at")
      (not (same-sched-client s seen)) (bad op (str "schedule " (pr-str seen) " is not " (pr-str s)))
      (and (:next-run-at s) (not= (c/n (:next-run-at s)) (c/n (:next-run-at seen))))
      (bad op "next-run-at changed without a client write")
      :else (assoc m :s (assoc s
                               :next-run-at (c/n (:next-run-at seen))
                               :created-at (c/n (:created-at seen))
                               :last-run-at nil)))))

(defn- install-schedule-response
  [op v]
  (let [s (:schedule v)]
    (cond
      (not= 200 (:status v)) (bad op (str "schedule.create status " (:status v)))
      (nil? s) (bad op "schedule.create 200 without a schedule")
      (not (same-sched-client v s)) (bad op "schedule.create stored different client fields")
      (some? (:last-run-at s)) (bad op "a new schedule already fired")
      (not (number? (:next-run-at s))) (bad op "a new schedule has no next-run-at")
      :else {:s (assoc (sched-client v)
                       :next-run-at (c/n (:next-run-at s))
                       :created-at (c/n (:created-at s))
                       :last-run-at nil)})))

(defn- install-schedule-request
  [v]
  {:s (assoc (sched-client v) :next-run-at nil :created-at nil :last-run-at nil)})

(defrecord ScheduleModel [s]
  Model
  (step [this op]
    (let [v (:value op)
          env (when (c/observed? v) (envelope-ok op v))]
      (or env
          (case (:f op)
            :create
            (cond
              (not (c/observed? v))
              (if s this (assoc this :s (:s (install-schedule-request v))))

              s
              (if (= 200 (:status v))
                (observe-schedule op this (:schedule v))
                (bad op (str "schedule.create status " (:status v))))

              :else
              (let [installed (install-schedule-response op v)]
                (if (model/inconsistent? installed)
                  installed
                  (assoc this :s (:s installed)))))

            :get
            (cond
              (not (c/observed? v)) this
              (= 404 (:status v)) (if s (bad op "schedule.get 404 but it exists") this)
              (= 200 (:status v)) (observe-schedule op this (:schedule v))
              :else (bad op (str "schedule.get status " (:status v))))

            :delete
            (cond
              (not (c/observed? v)) (if s (assoc this :s nil) this)
              (= 200 (:status v)) (if s (assoc this :s nil) (bad op "schedule.delete 200 but nothing was there"))
              (= 404 (:status v)) (if s (bad op "schedule.delete 404 but it exists") this)
              :else (bad op (str "schedule.delete status " (:status v))))

            this))))

  Object
  (toString [_] (pr-str s)))

(defn schedule
  []
  (ScheduleModel. nil))

(defn step
  "One transition of a model. An illegal transition is an Inconsistent value."
  [m op]
  (.step ^Model m op))

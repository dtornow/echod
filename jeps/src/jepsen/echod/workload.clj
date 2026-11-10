(ns jepsen.echod.workload
  "The histories. Each key is one document machine, and several keys share
  an origin so a conditional write has a neighbour to clobber.

  Params and values are strings. A map would come back from the codec with
  string keys, and a pass would then depend on how JSON objects are
  compared rather than on the pipeline."
  (:refer-clojure :exclude [promise])
  (:require [jepsen.echod.checker :as checker]
            [jepsen.echod.client :as client]
            [jepsen.echod.core :as c]
            [jepsen.echod.model :as model]
            [jepsen.echod.nemesis :as nemesis]
            [jepsen.echod.worker :as worker]
            [jepsen.generator :as gen]
            [jepsen.independent :as ind]))

(def workloads
  "Workloads a single test can name."
  #{:promise :task :idempotence :schedule :deadline :indefinite})

(def suite-workloads
  "What `test-all` runs. Indefinite is opt-in: it shortens the client
  timeout so calls come back `:info`."
  [:promise :task :idempotence :schedule :deadline])

(defn- later
  [ms]
  (+ (System/currentTimeMillis) (long ms)))

(defn- per-key
  [opts fgen]
  (ind/concurrent-generator
   (long (:key-concurrency opts 2))
   (range (long (:key-count opts 40)))
   fgen))

(defn- scope
  []
  {"resonate:scope" "global"})

(defn- settle-state
  []
  (rand-nth ["resolved" "rejected" "rejected_canceled"]))

(defn nemesis-gen
  "Quiet, then faults, then heal, then a pause so the final reads find the
  nodes up. The client generator stops before this pause; the phase barrier
  holds the clients until it is over."
  [opts]
  (let [t (long (:time-limit opts 60))
        quiet (long (:initial-quiet-period opts 5))
        heal (long (:heal-time opts 8))
        interval (long (:nemesis-interval opts 10))
        fault-dt (max 1 (- t quiet heal))
        steps (vec (mapcat (fn [fault]
                             (let [[start stop] (get nemesis/fault-ops fault)]
                               [(gen/sleep interval)
                                {:type :info :f start}
                                (gen/sleep interval)
                                {:type :info :f stop}]))
                           (:nemesis opts)))]
    (gen/phases
     (gen/sleep quiet)
     (gen/time-limit fault-dt (gen/cycle steps))
     {:type :info :f :heal}
     (gen/sleep heal))))

(defn generator
  "Client traffic, the nemesis beside it, then one read of every key."
  [opts client-gen final-gen]
  (let [t (long (:time-limit opts 60))
        heal (if (seq (:nemesis opts)) (long (:heal-time opts 8)) 0)
        client-dt (max 1 (- t heal))
        clients (gen/time-limit client-dt
                                (gen/stagger (/ 1.0 (double (:rate opts 30)))
                                             client-gen))]
    (gen/phases
     (if (seq (:nemesis opts))
       (gen/nemesis (nemesis-gen opts) clients)
       clients)
     (gen/log "Final reads")
     (gen/time-limit (long (:final-time-limit opts 30))
                     (gen/clients final-gen)))))

(defn- finals
  [opts f value]
  (gen/mix
   (mapv (fn [k]
           {:f f
            :value (ind/tuple k (value k))})
         (range (long (:key-count opts 40))))))

(defn- promise-body
  [opts k id]
  {:id id
   :timeout-at (later (:promise-timeout-ms opts 3600000))
   :param (str "k" k)
   :tags (scope)})

;; ---------------------------------------------------------------------------
;; promise
;; ---------------------------------------------------------------------------

(defn promise-client
  [opts]
  (per-key opts
           (fn [k]
             (let [id (c/promise-id opts k)]
               (gen/limit (long (:ops-per-key opts 20))
                          (gen/mix
                           [(fn [] {:f :create :value (promise-body opts k id)})
                            (fn [] {:f :get :value {:id id}})
                            (fn [] {:f :settle
                                    :value {:id id
                                            :state (settle-state)
                                            :value (str "s" k)}})
                            (fn [] {:f :listen :value {:id id}})]))))))

(defn promise-final
  [opts]
  (finals opts :get (fn [k] {:id (c/promise-id opts k) :final? true})))

(defn promise
  [opts]
  {:client (client/client nil)
   :client-gen (promise-client opts)
   :final-gen (promise-final opts)
   :checker (checker/suite
             {:model (model/promise)
              :required [:create :get :settle :listen]
              :claim-text checker/linear-claim
              :timeout-ms (:checker-timeout opts 30000)})})

;; ---------------------------------------------------------------------------
;; task
;; ---------------------------------------------------------------------------

(defn- task-create
  [opts k id]
  {:id id
   :timeout-at (later (:promise-timeout-ms opts 3600000))
   :param (str "k" k)
   :tags {"resonate:scope" "global"
          "resonate:target" (or (worker/url) "http://127.0.0.1:9/")}
   :target? true})

(defn- task-op
  [versions k id pid]
  (let [v (long (or (get @versions k) 0))
        state (settle-state)]
    (rand-nth
     [{:f :acquire :value {:id id :version v :pid pid :ttl 3600000}}
      {:f :release :value {:id id :version v}}
      {:f :fulfill :value {:id id :version v :state state :value (str "f" k)}}
      {:f :heartbeat :value {:id id :version v :pid pid}}
      {:f :get :value {:id id}}
      {:f :task-get :value {:id id}}
      {:f :listen :value {:id id}}
      {:f :settle :value {:id id :state state :value (str "s" k)}}])))

(defn task-client
  [opts versions]
  (per-key opts
           (fn [k]
             (let [id (c/promise-id opts k)
                   pid (str "pid-" k)
                   n (atom 0)]
               (gen/limit (long (:ops-per-key opts 20))
                          (fn []
                            (if (<= (swap! n inc) 2)
                              {:f :create :value (task-create opts k id)}
                              (task-op versions k id pid))))))))

(defn task-final
  [opts]
  (gen/mix
   (mapv (fn [[f k]]
           {:f f
            :value (ind/tuple k {:id (c/promise-id opts k) :final? true})})
         (for [f [:get :task-get]
               k (range (long (:key-count opts 40)))]
           [f k]))))

(defn task
  [opts]
  (let [versions (atom {})]
    {:client (client/client versions)
     :client-gen (task-client opts versions)
     :final-gen (task-final opts)
     :checker (checker/suite
               {:model (model/promise)
                :required [:create :acquire :release :fulfill :heartbeat :task-get :get]
                :claim-text checker/linear-claim
                :timeout-ms (:checker-timeout opts 30000)})}))

;; ---------------------------------------------------------------------------
;; idempotence
;; ---------------------------------------------------------------------------

(defn idempotence-client
  [opts]
  (per-key opts
           (fn [k]
             (let [id (c/promise-id opts k)
                   timeout (later (:promise-timeout-ms opts 3600000))
                   a {:id id :timeout-at timeout :param (str "a" k) :tags (scope)}
                   b {:id id :timeout-at (+ timeout 50) :param (str "b" k) :tags (scope)}]
               (gen/limit (long (:ops-per-key opts 20))
                          (gen/mix
                           [(gen/repeat {:f :create :value a})
                            (gen/repeat {:f :create :value b})
                            (gen/repeat {:f :settle :value {:id id :state "resolved" :value (str "sa" k)}})
                            (gen/repeat {:f :settle :value {:id id :state "rejected" :value (str "sb" k)}})
                            (gen/repeat {:f :get :value {:id id}})]))))))

(defn idempotence
  [opts]
  {:client (client/client nil)
   :client-gen (idempotence-client opts)
   :final-gen (promise-final opts)
   :checker (checker/suite
             {:model (model/promise)
              :required [:create :get :settle]
              :claim-text checker/linear-claim
              :timeout-ms (:checker-timeout opts 30000)})})

;; ---------------------------------------------------------------------------
;; schedule
;; ---------------------------------------------------------------------------

(defn- schedule-tags
  "Admission refuses a schedule whose promise has no `resonate:target`.
  The cron is yearly, so the target is never called."
  []
  {"resonate:scope" "global"
   "resonate:target" (or (worker/url) "http://127.0.0.1:9/")})

(defn schedule-client
  [opts]
  (per-key opts
           (fn [k]
             (let [id (c/schedule-id k)
                   a {:id id
                      :schedule? true
                      :cron "0 0 0 1 1 *"
                      :promise-id (str "o" k ":born")
                      :promise-timeout 60000
                      :param (str "a" k)
                      :tags (schedule-tags)}
                   b (assoc a :param (str "b" k))]
               (gen/limit (long (:ops-per-key opts 20))
                          (gen/mix
                           [(gen/repeat {:f :create :value a})
                            (gen/repeat {:f :create :value b})
                            (gen/repeat {:f :get :value {:id id :schedule? true}})
                            (gen/repeat {:f :delete :value {:id id :schedule? true}})]))))))

(defn schedule-final
  [opts]
  (finals opts :get (fn [k] {:id (c/schedule-id k) :schedule? true :final? true})))

(defn schedule
  [opts]
  {:client (client/client nil)
   :client-gen (schedule-client opts)
   :final-gen (schedule-final opts)
   :checker (checker/suite
             {:model (model/schedule)
              :schedule? true
              :required [:create :get :delete]
              :claim-text checker/linear-claim
              :timeout-ms (:checker-timeout opts 30000)})})

;; ---------------------------------------------------------------------------
;; deadline
;; ---------------------------------------------------------------------------

(defn deadline-client
  [opts]
  (per-key opts
           (fn [k]
             (let [id (c/promise-id opts k)
                   timer? (even? (long k))
                   tags (if timer?
                          {"resonate:timer" "true" "resonate:scope" "global"}
                          (scope))]
               (gen/limit (long (:ops-per-key opts 20))
                          (gen/mix
                           [(fn [] {:f :create
                                    :value {:id id
                                            :timeout-at (later (:deadline-ms opts 1500))
                                            :param (str "k" k)
                                            :tags tags}})
                            (fn [] {:f :get :value {:id id}})
                            (fn [] {:f :listen :value {:id id}})
                            (fn [] {:f :settle
                                    :value {:id id
                                            :state (settle-state)
                                            :value (str "s" k)}})]))))))

(defn deadline
  [opts]
  {:client (client/client nil)
   :client-gen (deadline-client opts)
   :final-gen (promise-final opts)
   :timer-bucket-ms 400
   :checker (checker/suite
             {:deadline? true
              :required [:create :get :listen]
              :claim-text checker/deadline-claim
              :timeout-ms (:checker-timeout opts 30000)})})

;; ---------------------------------------------------------------------------
;; indefinite
;; ---------------------------------------------------------------------------

(defn indefinite
  "The promise workload with a short client timeout. A call that comes back
  without an answer is `:info`: it may have committed. The final reads use
  the long timeout."
  [opts]
  (assoc (promise opts) :client-timeout 50))

(def by-name
  {:promise promise
   :task task
   :idempotence idempotence
   :schedule schedule
   :deadline deadline
   :indefinite indefinite})

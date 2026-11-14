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
  #{:promise :task :idempotence :schedule :deadline :indefinite :brutal})

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

;; ---------------------------------------------------------------------------
;; brutal: every method, promise and schedule keys together
;; ---------------------------------------------------------------------------

(defn- schedule-key?
  "The last quarter of the keys are schedules. The rest are promises, and
  each of those origins is a whole group, so a callback's awaiter is a
  promise this test also creates."
  [opts k]
  (>= (long k) (long (quot (* 3 (long (:key-count opts 40))) 4))))

(defn- brutal-keys
  "Schedule keys first, so a thread group creates and deletes them before
  the promise keys fill the rest of the run. The key list is visited in
  order, and a key that starts late otherwise never runs."
  [opts]
  (let [n (long (:key-count opts 40))
        sched (filterv #(schedule-key? opts %) (range n))
        prom (filterv #(not (schedule-key? opts %)) (range n))]
    (concat (take 8 sched) prom (drop 8 sched))))

(defn- child-id
  "A promise in this key's origin that no generator settles. A fence creates
  it and a suspend waits on it, so the suspend is not woken by another key."
  [opts k]
  (let [id (c/promise-id opts k)
        colon (.indexOf ^String id ":")]
    (str (subs id 0 colon) ":c" k)))

(defn- sibling-id
  "Another promise key in the same origin. A callback's awaiter has to be a
  targeted promise, and it cannot be the awaited id."
  [opts k]
  (let [share (long (:share opts 4))
        origin (quot (long k) share)
        mates (vec (filter (fn [i]
                             (and (= origin (quot (long i) share))
                                  (not (schedule-key? opts i))))
                           (range (long (:key-count opts 40)))))
        mates (if (seq mates) mates [k])
        i (.indexOf ^java.util.List mates (long k))
        i (if (neg? i) 0 i)]
    (c/promise-id opts (nth mates (mod (inc i) (count mates))))))

(defn- brutal-task-op
  [opts versions k id pid]
  (let [v (long (or (get @versions k) 0))
        state (settle-state)
        timeout (later (:promise-timeout-ms opts 3600000))]
    (rand-nth
     [{:f :create :value (task-create opts k id)}
      {:f :create :value (assoc (task-create opts k id)
                                :param (str "b" k)
                                :timeout-at (+ timeout 50))}
      {:f :task-create :value (assoc (task-create opts k id) :pid pid :ttl 3600000)}
      {:f :get :value {:id id}}
      {:f :task-get :value {:id id}}
      {:f :listen :value {:id id}}
      {:f :settle :value {:id id :state state :value (str "s" k)}}
      {:f :callback :value {:id id :awaited id :awaiter (sibling-id opts k)}}
      {:f :acquire :value {:id id :version v :pid pid :ttl 3600000}}
      {:f :release :value {:id id :version v}}
      {:f :fulfill :value {:id id :version v :state state :value (str "f" k)}}
      {:f :heartbeat :value {:id id :version v :pid pid}}
      {:f :halt :value {:id id}}
      {:f :continue :value {:id id}}
      {:f :fence :value {:id id
                         :version v
                         :timeout-at timeout
                         :child (child-id opts k)
                         :child-param (str "c" k)}}
      {:f :suspend :value {:id id :version v :awaited (child-id opts k)}}
      {:f :search :value {:id id :search "promise"}}
      {:f :search :value {:id id :search "task"}}])))

(defn- scripted
  "The first ops on a key, in order, then the random mix. One thread on the
  key makes the order real: task.create leaves the lease held, so the fence
  and the suspend that follow can succeed, and halt then continue."
  [script then]
  (let [left (atom script)]
    (fn []
      (if-let [op (first @left)]
        (do (swap! left rest) (op))
        (then)))))

(defn brutal-client
  [opts versions]
  (ind/concurrent-generator
   (long (:key-concurrency opts 2))
   (brutal-keys opts)
   (fn [k]
     (if (schedule-key? opts k)
       (let [id (c/schedule-id k)
             a {:id id
                :schedule? true
                :cron "0 0 0 1 1 *"
                :promise-id (str "o" k ":born")
                :promise-timeout 60000
                :param (str "a" k)
                :tags (schedule-tags)}
             b (assoc a :param (str "b" k))
             once (fn [v] (fn [] v))]
         (gen/limit (long (:ops-per-key opts 20))
                    (scripted
                     [(once {:f :create :value a})
                      (once {:f :get :value {:id id :schedule? true}})
                      (once {:f :delete :value {:id id :schedule? true}})
                      (once {:f :create :value b})
                      (once {:f :search :value {:id id :schedule? true :search "schedule"}})]
                     (fn []
                       (rand-nth [{:f :create :value a}
                                  {:f :create :value b}
                                  {:f :get :value {:id id :schedule? true}}
                                  {:f :delete :value {:id id :schedule? true}}
                                  {:f :search :value {:id id :schedule? true :search "schedule"}}])))))
       (let [id (c/promise-id opts k)
             pid (str "pid-" k)
             hold (fn [f]
                    (fn []
                      (let [v (long (or (get @versions k) 0))
                            timeout (later (:promise-timeout-ms opts 3600000))]
                        (case f
                          :task-create {:f :task-create :value (assoc (task-create opts k id) :pid pid :ttl 3600000)}
                          :create {:f :create :value (task-create opts k id)}
                          :fence {:f :fence :value {:id id :version v :timeout-at timeout
                                                    :child (child-id opts k) :child-param (str "c" k)}}
                          :suspend {:f :suspend :value {:id id :version v :awaited (child-id opts k)}}
                          :halt {:f :halt :value {:id id}}
                          :continue {:f :continue :value {:id id}}))))]
         (gen/limit (long (:ops-per-key opts 20))
                    (scripted
                     [(hold :task-create) (hold :create) (hold :fence) (hold :suspend)
                      (hold :halt) (hold :continue)]
                     (fn [] (brutal-task-op opts versions k id pid)))))))))

(defn brutal-final
  [opts]
  (gen/mix
   (mapv (fn [k]
           (if (schedule-key? opts k)
             {:f :get
              :value (ind/tuple k {:id (c/schedule-id k) :schedule? true :final? true})}
             {:f :get
              :value (ind/tuple k {:id (c/promise-id opts k) :final? true})}))
         (range (long (:key-count opts 40))))))

(defn brutal
  [opts]
  (let [versions (atom {})]
    {:client (client/client versions)
     :client-gen (brutal-client opts versions)
     :final-gen (brutal-final opts)
     :checker (checker/suite
               {:model (model/brutal)
                :required [:create :get :settle :listen :callback
                           :task-create :acquire :release :fulfill :heartbeat
                           :task-get :halt :continue :suspend :fence :delete]
                :claim-text checker/linear-claim
                :timeout-ms (:checker-timeout opts 30000)})}))

(def by-name
  {:promise promise
   :task task
   :idempotence idempotence
   :schedule schedule
   :deadline deadline
   :indefinite indefinite
   :brutal brutal})

(ns jepsen.echod.model-test
  "The document machine, stepped by hand and searched by Knossos.

  A history here is the same shape a client records: an `:ok` value is the
  request merged with the status, the node header, and the record. An
  `:info` value is the request alone."
  (:require [clojure.test :refer [deftest is testing]]
            [jepsen.checker :as jchecker]
            [jepsen.echod.checker :as checker]
            [jepsen.echod.core :as c]
            [jepsen.echod.model :as model]
            [knossos.model :as kmodel]))

(def id "o0:p0")

(defn base
  [extra]
  (merge {:id id
          :timeout-at 5000
          :param "a"
          :tags {"resonate:scope" "global"}}
         extra))

(defn promise-of
  ([state value settled]
   (promise-of state value settled {"resonate:scope" "global"}))
  ([state value settled tagm]
   {:id id
    :state state
    :param "a"
    :value value
    :timeout-at 5000
    :tags (c/tags tagm)
    :created-at 1000
    :settled-at settled}))

(defn done
  "An `:ok` whose value is the request plus the envelope."
  [f req status promise]
  {:type :ok :process 0 :f f
   :value (cond-> (merge req {:http status :status status :node "n1"})
            promise (assoc :promise promise))})

(defn step
  [m f req status promise]
  (model/step m (done f req status promise)))

(defn created
  []
  (step (model/promise) :create (base {}) 200 (promise-of "pending" nil nil)))

(defn lin
  [m ops]
  (jchecker/check (checker/bounded-linear m 10000) {} ops {}))

(deftest create-then-get
  (let [m (created)
        m (step m :get (base {}) 200 (promise-of "pending" nil nil))]
    (is (instance? jepsen.echod.model.PromiseModel m))
    (is (not (kmodel/inconsistent? m)))
    (is (= "pending" (:state (:p m))))
    (is (= 1000 (:created-at (:p m))))))

(deftest idempotent-create-returns-the-winner
  (let [m (created)
        other (base {:param "b" :timeout-at 6000})
        m (step m :create other 200 (promise-of "pending" nil nil))]
    (is (not (kmodel/inconsistent? m)))
    (is (= "a" (:param (:p m))))))

(deftest two-creates-cannot-both-win
  (let [m (created)
        other (base {:param "b"})
        won (assoc (promise-of "pending" nil nil) :param "b")
        m (step m :create other 200 won)]
    (is (kmodel/inconsistent? m))))

(deftest settle-then-a-second-settle-returns-the-first
  (let [m (created)
        m (step m :settle {:id id :state "resolved" :value "sa"} 200
                (promise-of "resolved" "sa" 2000))
        m (step m :settle {:id id :state "rejected" :value "sb"} 200
                (promise-of "resolved" "sa" 2000))]
    (is (not (kmodel/inconsistent? m)))
    (is (= "resolved" (:state (:p m))))
    (is (= "sa" (:value (:p m))))))

(deftest a-second-terminal-state-is-rejected
  (let [m (created)
        m (step m :settle {:id id :state "resolved" :value "sa"} 200
                (promise-of "resolved" "sa" 2000))
        m (step m :settle {:id id :state "rejected" :value "sb"} 200
                (promise-of "rejected" "sb" 2000))]
    (is (kmodel/inconsistent? m))))

(deftest settle-of-nothing-is-404
  (is (not (kmodel/inconsistent?
            (step (model/promise) :settle {:id id :state "resolved" :value "sa"} 404 nil))))
  (is (kmodel/inconsistent?
       (step (created) :settle {:id id :state "resolved" :value "sa"} 404 nil))))

(deftest get-of-nothing-is-404
  (is (not (kmodel/inconsistent?
            (step (model/promise) :get (base {}) 404 nil))))
  (is (kmodel/inconsistent?
       (step (created) :get (base {}) 404 nil))))

(deftest the-two-copies-of-the-status-agree
  (is (kmodel/inconsistent?
       (model/step (model/promise)
                   {:type :ok :f :get :process 0
                    :value (assoc (base {}) :http 200 :status 404 :node "n1")})))
  (is (kmodel/inconsistent?
       (model/step (created)
                   {:type :ok :f :get :process 0
                    :value (merge (base {})
                                  {:http 200 :status 200 :node ""
                                   :promise (promise-of "pending" nil nil)})}))))

(deftest an-info-create-is-a-model
  (let [m (model/step (model/promise)
                      {:type :info :f :create :process 0 :value (base {})})]
    (is (instance? jepsen.echod.model.PromiseModel m))
    (is (= "pending" (:state (:p m))))
    (is (nil? (:created-at (:p m))))
    (let [m (step m :get (base {}) 200 (promise-of "pending" nil nil))]
      (is (not (kmodel/inconsistent? m)))
      (is (= 1000 (:created-at (:p m)))))))

(def target-tags
  {"resonate:scope" "global"
   "resonate:target" "http://127.0.0.1:9/"})

(defn- target
  []
  (base {:tags target-tags}))

(defn- seen
  [state value settled]
  (promise-of state value settled target-tags))

(defn- task
  [state version pid]
  {:state state :version version :pid pid})

(deftest acquire-bumps-the-version
  (let [m (step (model/promise) :create (target) 200 (seen "pending" nil nil))
        req {:id id :version 0 :pid "p" :ttl 3600000}
        m (model/step m {:type :ok :f :acquire :process 0
                         :value (assoc req :http 200 :status 200 :node "n1"
                                       :promise (seen "pending" nil nil)
                                       :task (task "acquired" 1 "p"))})]
    (is (not (kmodel/inconsistent? m)))
    (is (= 1 (:version (:task (:p m)))))
    (is (= "acquired" (:state (:task (:p m)))))
    (testing "a second acquire at the old version is a 409"
      (let [again (model/step m {:type :ok :f :acquire :process 1
                                 :value (assoc req :http 409 :status 409 :node "n1")})]
        (is (not (kmodel/inconsistent? again)))))
    (testing "a 409 while the task is still pending at that version is a bug"
      (let [fresh (step (model/promise) :create (target) 200 (seen "pending" nil nil))
            bad (model/step fresh {:type :ok :f :acquire :process 0
                                   :value (assoc req :http 409 :status 409 :node "n1")})]
        (is (kmodel/inconsistent? bad))))))

(deftest fulfill-settles-and-fulfills
  (let [m (step (model/promise) :create (target) 200 (seen "pending" nil nil))
        m (model/step m {:type :ok :f :acquire :process 0
                         :value {:id id :version 0 :pid "p" :ttl 3600000
                                 :http 200 :status 200 :node "n1"
                                 :promise (seen "pending" nil nil)
                                 :task (task "acquired" 1 "p")}})
        m (model/step m {:type :ok :f :fulfill :process 0
                         :value {:id id :version 1 :state "resolved" :value "done"
                                 :http 200 :status 200 :node "n1"
                                 :promise (seen "resolved" "done" 2000)}})]
    (is (not (kmodel/inconsistent? m)))
    (is (= "resolved" (:state (:p m))))
    (is (= "fulfilled" (:state (:task (:p m)))))))

(deftest release-returns-the-lease
  (let [m (step (model/promise) :create (target) 200 (seen "pending" nil nil))
        m (model/step m {:type :ok :f :acquire :process 0
                         :value {:id id :version 0 :pid "p" :ttl 3600000
                                 :http 200 :status 200 :node "n1"
                                 :promise (seen "pending" nil nil)
                                 :task (task "acquired" 1 "p")}})
        m (model/step m {:type :ok :f :release :process 0
                         :value {:id id :version 1 :http 200 :status 200 :node "n1"}})
        m (model/step m {:type :ok :f :task-get :process 0
                         :value {:id id :http 200 :status 200 :node "n1"
                                 :task (task "pending" 1 nil)}})]
    (is (not (kmodel/inconsistent? m)))
    (is (= "pending" (:state (:task (:p m)))))
    (is (= 1 (:version (:task (:p m)))))))

(deftest release-without-a-lease-cannot-be-200
  (let [m (step (model/promise) :create (target) 200 (seen "pending" nil nil))
        m (model/step m {:type :ok :f :release :process 0
                         :value {:id id :version 0 :http 200 :status 200 :node "n1"}})]
    (is (kmodel/inconsistent? m))))

(deftest heartbeat-does-not-move-the-record
  (let [m (created)
        m (model/step m {:type :ok :f :heartbeat :process 0
                         :value {:id id :pid "p" :version 0
                                 :http 200 :status 200 :node "n1"}})]
    (is (not (kmodel/inconsistent? m)))
    (is (= "pending" (:state (:p m))))))

(defn sched
  [extra]
  (merge {:id "sched-0"
          :schedule? true
          :cron "0 0 0 1 1 *"
          :promise-id "o0:born"
          :promise-timeout 60000
          :param "a"
          :tags {"resonate:scope" "global"}
          :next-run-at 9000000000000
          :created-at 1000
          :last-run-at nil}
         extra))

(deftest schedule-create-get-delete
  (let [body (select-keys (sched {}) [:id :schedule? :cron :promise-id :promise-timeout :param :tags])
        m (model/step (model/schedule)
                      {:type :ok :f :create :process 0
                       :value (assoc body :http 200 :status 200 :node "n1" :schedule (sched {}))})
        m (model/step m {:type :ok :f :get :process 0
                         :value (assoc body :http 200 :status 200 :node "n1" :schedule (sched {}))})
        m (model/step m {:type :ok :f :delete :process 0
                         :value (assoc body :http 200 :status 200 :node "n1")})
        m (model/step m {:type :ok :f :get :process 1
                         :value (assoc body :http 404 :status 404 :node "n1")})]
    (is (instance? jepsen.echod.model.ScheduleModel m))
    (is (not (kmodel/inconsistent? m)))
    (is (nil? (:s m)))))

(deftest a-schedule-that-fires-is-rejected
  (let [body (select-keys (sched {}) [:id :schedule? :cron :promise-id :promise-timeout :param :tags])
        m (model/step (model/schedule)
                      {:type :ok :f :create :process 0
                       :value (assoc body :http 200 :status 200 :node "n1"
                                     :schedule (sched {:last-run-at 1000}))})]
    (is (kmodel/inconsistent? m))))

(deftest a-crashed-create-that-a-later-read-shows
  (let [req (base {})
        seen (promise-of "pending" nil nil)
        r (lin (model/promise)
               [{:process 0 :type :invoke :f :create :value req}
                {:process 0 :type :info :f :create :value req :error :timeout}
                {:process 0 :type :invoke :f :get :value {:id id}}
                {:process 0 :type :ok :f :get
                 :value (assoc {:id id} :http 200 :status 200 :node "n1" :promise seen)}])]
    (is (true? (:valid? r)) (pr-str r))))

(deftest a-crashed-create-that-never-landed
  (let [req (base {})
        r (lin (model/promise)
               [{:process 0 :type :invoke :f :create :value req}
                {:process 0 :type :info :f :create :value req :error :timeout}
                {:process 0 :type :invoke :f :get :value {:id id}}
                {:process 0 :type :ok :f :get
                 :value {:id id :http 404 :status 404 :node "n1"}}])]
    (is (true? (:valid? r)) (pr-str r))))

(deftest concurrent-creates-must-agree-on-a-winner
  (let [a (base {:param "a"})
        b (base {:param "b"})
        win (fn [param]
              (assoc (promise-of "pending" nil nil) :param param))
        both-win (lin (model/promise)
                      [{:process 0 :type :invoke :f :create :value a}
                       {:process 1 :type :invoke :f :create :value b}
                       {:process 0 :type :ok :f :create
                        :value (assoc a :http 200 :status 200 :node "n1" :promise (win "a"))}
                       {:process 1 :type :ok :f :create
                        :value (assoc b :http 200 :status 200 :node "n1" :promise (win "b"))}])
        one-wins (lin (model/promise)
                      [{:process 0 :type :invoke :f :create :value a}
                       {:process 1 :type :invoke :f :create :value b}
                       {:process 0 :type :ok :f :create
                        :value (assoc a :http 200 :status 200 :node "n1" :promise (win "a"))}
                       {:process 1 :type :ok :f :create
                        :value (assoc b :http 200 :status 200 :node "n1" :promise (win "a"))}])]
    (is (false? (:valid? both-win)) (pr-str both-win))
    (is (true? (:valid? one-wins)) (pr-str one-wins))))

(defn- held
  []
  (let [m (step (model/promise) :create (target) 200 (seen "pending" nil nil))]
    (model/step m {:type :ok :f :acquire :process 0
                   :value {:id id :version 0 :pid "p" :ttl 3600000
                           :http 200 :status 200 :node "n1"
                           :promise (seen "pending" nil nil)
                           :task (task "acquired" 1 "p")}})))

(deftest halt-and-continue-round-trip
  (let [m (held)
        m (model/step m {:type :ok :f :halt :process 0
                         :value {:id id :http 200 :status 200 :node "n1"}})
        m (model/step m {:type :ok :f :continue :process 0
                         :value {:id id :http 200 :status 200 :node "n1"}})
        m (model/step m {:type :ok :f :task-get :process 0
                         :value {:id id :http 200 :status 200 :node "n1"
                                 :task (task "pending" 1 nil)}})]
    (is (not (kmodel/inconsistent? m)))
    (is (= "pending" (:state (:task (:p m)))))))

(deftest halt-of-a-fulfilled-task-is-409
  (let [m (held)
        m (model/step m {:type :ok :f :fulfill :process 0
                         :value {:id id :version 1 :state "resolved" :value "done"
                                 :http 200 :status 200 :node "n1"
                                 :promise (seen "resolved" "done" 2000)}})
        ok (model/step m {:type :ok :f :halt :process 0
                          :value {:id id :http 409 :status 409 :node "n1"}})
        bad (model/step m {:type :ok :f :halt :process 0
                           :value {:id id :http 200 :status 200 :node "n1"}})]
    (is (not (kmodel/inconsistent? ok)))
    (is (kmodel/inconsistent? bad))))

(deftest suspend-and-fence-need-the-lease
  (let [m (held)
        suspended (model/step m {:type :ok :f :suspend :process 0
                                 :value {:id id :version 1 :awaited "o0:c0"
                                         :http 200 :status 200 :node "n1"}})
        fenced (model/step m {:type :ok :f :fence :process 0
                              :value {:id id :version 1 :child "o0:c0"
                                      :http 200 :status 200 :node "n1"}})
        bare (step (model/promise) :create (target) 200 (seen "pending" nil nil))
        no-lease (model/step bare {:type :ok :f :fence :process 0
                                   :value {:id id :version 0 :child "o0:c0"
                                           :http 200 :status 200 :node "n1"}})]
    (is (not (kmodel/inconsistent? suspended)))
    (is (= "suspended" (:state (:task (:p suspended)))))
    (is (not (kmodel/inconsistent? fenced)))
    (is (= "acquired" (:state (:task (:p fenced)))))
    (is (kmodel/inconsistent? no-lease))))

(deftest task-create-acquires-a-pending-task-without-a-version
  (let [m (step (model/promise) :create (target) 200 (seen "pending" nil nil))
        req (assoc (target) :pid "p" :ttl 3600000)
        m (model/step m {:type :ok :f :task-create :process 0
                         :value (assoc req :http 200 :status 200 :node "n1"
                                       :promise (seen "pending" nil nil)
                                       :task (task "acquired" 1 "p"))})
        again (model/step m {:type :ok :f :task-create :process 1
                             :value (assoc req :param "b" :http 409 :status 409 :node "n1")})]
    (is (not (kmodel/inconsistent? m)))
    (is (= 1 (:version (:task (:p m)))))
    (is (not (kmodel/inconsistent? again)))))

(deftest task-create-of-a-fresh-id-acquires-it
  (let [req (assoc (target) :pid "p" :ttl 3600000)
        m (model/step (model/promise)
                      {:type :ok :f :task-create :process 0
                       :value (assoc req :http 200 :status 200 :node "n1"
                                     :promise (seen "pending" nil nil)
                                     :task (task "acquired" 1 "p"))})]
    (is (not (kmodel/inconsistent? m)))
    (is (= "acquired" (:state (:task (:p m)))))
    (is (= 1 (:version (:task (:p m)))))))

(deftest a-callback-is-a-read-and-a-search-is-a-refusal
  (let [m (created)
        m (model/step m {:type :ok :f :callback :process 0
                         :value (assoc (base {}) :awaited id :awaiter "o0:p1"
                                       :http 200 :status 200 :node "n1"
                                       :promise (promise-of "pending" nil nil))})
        m (model/step m {:type :ok :f :search :process 0
                         :value {:id id :search "promise"
                                 :http 403 :status 403 :node "n1"}})]
    (is (not (kmodel/inconsistent? m)))
    (is (kmodel/inconsistent?
         (model/step m {:type :ok :f :search :process 0
                        :value {:id id :search "promise"
                                :http 200 :status 200 :node "n1"}})))))

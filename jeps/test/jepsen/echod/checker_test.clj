(ns jepsen.echod.checker-test
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest is]]
            [jepsen.checker :as checker]
            [jepsen.echod.checker :as ec]
            [jepsen.echod.cli :as cli]
            [jepsen.echod.client :as client]
            [jepsen.echod.core :as c]
            [jepsen.independent :as ind]))

(def id "o0:p0")

(def tags (c/tags {"resonate:scope" "global"}))

(defn rec
  [state value]
  {:id id :state state :param "a" :value value
   :timeout-at 5000 :tags tags :created-at 1000
   :settled-at (when (not= "pending" state) 2000)})

(defn ok
  [process f value]
  {:type :ok :process process :f f :value value})

(defn read-of
  [process state value]
  (ok process :get {:id id :http 200 :status 200 :node "n1" :promise (rec state value)}))

(deftest conflicting-terminal-states-fail-the-invariants
  (let [h [{:type :invoke :process 0 :f :settle :value {:id id :state "resolved" :value "a"}}
           (read-of 0 "resolved" "a")
           {:type :invoke :process 1 :f :get :value {:id id}}
           (read-of 1 "rejected" "b")]
        r (checker/check (ec/invariants) {} h {})]
    (is (false? (:valid? r)) (pr-str r))))

(deftest a-stable-terminal-state-passes
  (let [h [{:type :invoke :process 0 :f :settle :value {:id id}}
           (read-of 0 "resolved" "a")
           {:type :invoke :process 1 :f :get :value {:id id}}
           (read-of 1 "resolved" "a")]
        r (checker/check (ec/invariants) {} h {})]
    (is (true? (:valid? r)) (pr-str r))))

(deftest duplicate-unblocks-fail
  (is (false? (:valid? (ec/check-unblocks
                        [{:id "a" :state "resolved"} {:id "a" :state "resolved"}]
                        [] []))))
  (is (false? (:valid? (ec/check-unblocks
                        [{:id "a" :state "resolved"}]
                        []
                        [(ok 0 :get {:status 200 :http 200 :node "n1"
                                     :promise {:id "a" :state "rejected" :value "x"}})]))))
  (is (true? (:valid? (ec/check-unblocks [] [{:id "a"} {:id "a"}] []))))
  (is (true? (:valid? (ec/check-unblocks
                       [{:id "a" :state "resolved"}]
                       []
                       [(ok 0 :get {:status 200 :http 200 :node "n1"
                                    :promise {:id "a" :state "resolved" :value "x"}})])))))

(deftest deadlines
  (let [create {:type :invoke :process 0 :f :create
                :value {:id id :tags {"resonate:scope" "global"} :param "a"}}
        timer-create (assoc-in create [:value :tags] {"resonate:timer" "true"
                                                      "resonate:scope" "global"})
        final (fn [state value]
                (ok 1 :get {:id id :final? true :http 200 :status 200 :node "n1"
                            :promise (rec state value)}))]
    (is (true? (:valid? (ec/check-deadline [create (final "rejected_timedout" nil)]))))
    (is (true? (:valid? (ec/check-deadline [timer-create (final "resolved" nil)]))))
    (is (false? (:valid? (ec/check-deadline [timer-create (final "rejected_timedout" nil)]))))
    (is (false? (:valid? (ec/check-deadline [create (final "resolved" nil)]))))
    (is (false? (:valid? (ec/check-deadline [create (final "pending" nil)]))))
    (is (= :unknown (:valid? (ec/check-deadline
                              [create
                               {:type :info :process 1 :f :get
                                :value {:id id :final? true} :error :timeout}]))))))

(deftest a-panic-in-the-log-fails
  (let [dir (io/file (System/getProperty "java.io.tmpdir")
                     (str "echod-jeps-" (System/nanoTime)))
        log (io/file dir "n1" "echod.log")]
    (.mkdirs (.getParentFile log))
    (spit log "normal line\nthread panicked at 'boom', src/lib.rs:1\n")
    (is (false? (:valid? (checker/check (ec/panic) {:runtime-dir dir} [] {}))))
    (spit log "normal line\n")
    (is (true? (:valid? (checker/check (ec/panic) {:runtime-dir dir} [] {}))))
    (doseq [f (reverse (file-seq dir))] (.delete f))))

(deftest exercised-wants-a-2xx
  (let [h [(ok 0 :create {:status 200 :http 200 :node "n1"})
           (ok 1 :get {:status 404 :http 404 :node "n1"})]
        r (checker/check (ec/exercised [:create :get]) {} h {})]
    (is (false? (:valid? r)))
    (is (= [:get] (:missing r)))))

(deftest client-timeouts
  (is (= :info (client/classify 503)))
  (is (= :ok (client/classify 200)))
  (is (= :ok (client/classify 404)))
  (is (= :ok (client/classify 409)))
  (is (= 8 (:attempts (client/call-budget {} {:value (ind/tuple 0 {:final? true})}))))
  (is (= 1 (:attempts (client/call-budget {:timeout 50} {:value (ind/tuple 0 {:id "a"})}))))
  (is (= 50 (:ms (client/call-budget {:timeout 50} {:value {:id "a"}})))))

(deftest concurrency-is-a-multiple-of-the-key-concurrency
  (is (= 6 (:concurrency (cli/align-concurrency {:concurrency 5 :key-concurrency 2}))))
  (is (= 4 (:concurrency (cli/align-concurrency {:concurrency 4 :key-concurrency 2})))))

(deftest promise-ids-share-an-origin
  (is (= "o0:p0" (c/promise-id {:share 4} 0)))
  (is (= "o0:p3" (c/promise-id {:share 4} 3)))
  (is (= "o1:p4" (c/promise-id {:share 4} 4))))

(def opts
  {:nodes ["n1" "n2"]
   :ssh {:dummy? true}
   :local? true
   :bin "/bin/true"
   :nemesis []
   :concurrency 2
   :key-concurrency 2
   :key-count 2
   :ops-per-key 2
   :rate 10
   :time-limit 5
   :timeout 1000
   :final-timeout 1000
   :checker-timeout 1000
   :heartbeat-ms 500
   :node-ttl-ms 2000
   :retry-timeout 60000
   :compact 0
   :base-port 18001
   :port 8001
   :worker-host "127.0.0.1"
   :rust-log "info"
   :client-nodes :all
   :share 4
   :promise-timeout-ms 3600000
   :deadline-ms 1500
   :final-time-limit 5
   :heal-time 1
   :initial-quiet-period 0
   :nemesis-interval 1
   :prefix "t/"
   :nemesis-target :minority})

(deftest the-test-map-names-the-pass
  (let [p (cli/echod-test (assoc opts :workload :promise))
        d (cli/echod-test (assoc opts :workload :deadline :nemesis [:kill]))
        i (cli/echod-test (assoc opts :workload :indefinite))]
    (is (= "echod-promise" (:name p)))
    (is (= 3600000 (:timer-bucket-ms p)))
    (is (= "echod-deadline-kill" (:name d)))
    (is (= 400 (:timer-bucket-ms d)))
    (is (= 50 (:timeout i)))
    (is (= 15 (count (cli/all-tests opts))))))

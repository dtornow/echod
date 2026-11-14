(ns jepsen.echod.wire-test
  (:require [cheshire.core :as json]
            [clojure.test :refer [deftest is]]
            [jepsen.echod.wire :as wire]))

(deftest a-create-is-one-envelope
  (let [body (json/parse-string
              (wire/encode {:f :create
                            :value {:id "o0:p0"
                                    :timeout-at 5000
                                    :param "a"}}
                           "http://127.0.0.1:9/"))]
    (is (= "promise.create" (get body "kind")))
    (is (= "2026-04-01" (get-in body ["head" "version"])))
    (is (= "o0:p0" (get-in body ["data" "id"])))
    (is (= 5000 (get-in body ["data" "timeoutAt"])))
    (is (= "a" (get-in body ["data" "param" "data"])))
    (is (= "global" (get-in body ["data" "tags" "resonate:scope"])))))

(deftest a-response-becomes-the-record-the-model-sees
  (let [parsed (wire/parse-response
                {:id "o0:p0" :param "a" :timeout-at 5000
                 :tags {"resonate:scope" "global"}}
                200
                {"x-echod-node" "n1"}
                {"kind" "promise.get"
                 "head" {"status" 200}
                 "data" {"promise" {"id" "o0:p0"
                                    "state" "pending"
                                    "param" {"data" "a"}
                                    "value" {}
                                    "timeoutAt" 5000
                                    "createdAt" 1000
                                    "tags" {"resonate:scope" "global"}}}})]
    (is (= 200 (:http parsed)))
    (is (= 200 (:status parsed)))
    (is (= "n1" (:node parsed)))
    (is (= "pending" (:state (:promise parsed))))
    (is (= "a" (:param (:promise parsed))))
    (is (nil? (:value (:promise parsed))))
    (is (= 5000 (:timeout-at (:promise parsed))))
    (is (= 1000 (:created-at (:promise parsed))))))

(deftest an-error-body-is-a-string
  (let [parsed (wire/parse-response
                {:id "missing"}
                404
                {"x-echod-node" "n2"}
                {"kind" "promise.get"
                 "head" {"status" 404}
                 "data" "Promise not found"})]
    (is (= 404 (:status parsed)))
    (is (= "Promise not found" (:error parsed)))
    (is (nil? (:promise parsed)))))

(deftest a-schedule-create-is-a-schedule
  (let [body (json/parse-string
              (wire/encode {:f :create
                            :value {:id "sched-0"
                                    :cron "0 0 0 1 1 *"
                                    :promise-id "o0:born"
                                    :promise-timeout 60000
                                    :param "a"
                                    :tags {"resonate:scope" "global"
                                           "resonate:target" "http://127.0.0.1:9/"}}}
                           nil))]
    (is (= "schedule.create" (get body "kind")))
    (is (= "0 0 0 1 1 *" (get-in body ["data" "cron"])))
    (is (= "o0:born" (get-in body ["data" "promiseId"])))
    (is (= "http://127.0.0.1:9/" (get-in body ["data" "promiseTags" "resonate:target"])))))

(deftest the-remaining-methods-are-envelopes
  (let [halt (json/parse-string (wire/encode {:f :halt :value {:id "o0:p0"}} nil))
        callback (json/parse-string
                  (wire/encode {:f :callback
                                :value {:awaited "o0:p0" :awaiter "o0:p1"}}
                               nil))
        search (json/parse-string
                (wire/encode {:f :search :value {:search "task"}} nil))
        fence (json/parse-string
               (wire/encode {:f :fence
                             :value {:id "o0:p0" :version 1 :timeout-at 5000
                                     :child "o0:c0" :child-param "c"}}
                            nil))]
    (is (= "task.halt" (get halt "kind")))
    (is (= "o0:p0" (get-in halt ["data" "id"])))
    (is (= "promise.register_callback" (get callback "kind")))
    (is (= "o0:p1" (get-in callback ["data" "awaiter"])))
    (is (= "task.search" (get search "kind")))
    (is (= "task.fence" (get fence "kind")))
    (is (= "promise.create" (get-in fence ["data" "action" "kind"])))
    (is (= "o0:c0" (get-in fence ["data" "action" "data" "id"])))))

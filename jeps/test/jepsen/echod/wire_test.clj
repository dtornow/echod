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

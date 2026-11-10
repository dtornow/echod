(ns jepsen.echod.nemesis-test
  (:require [clojure.test :refer [deftest is]]
            [jepsen.echod.nemesis :as n]))

(deftest a-partition-names-the-store-port
  (is (= [:iptables :-A :OUTPUT :-p :tcp :-d "10.0.3.1" :--dport "18014" :-j :DROP]
         (vec (n/partition-args "10.0.3.1" 18014))))
  (is (= [:iptables :-A :OUTPUT :-p :tcp :-d "10.0.3.1" :-j :DROP]
         (vec (n/partition-args "10.0.3.1" nil))))
  (is (= 18014 (n/store-port {:endpoint "http://10.0.3.1:18014"})))
  (is (nil? (n/store-port {:endpoint "http://10.0.3.1"}))))

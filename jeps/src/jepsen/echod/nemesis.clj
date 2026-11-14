(ns jepsen.echod.nemesis
  "Faults from outside the process.

  echod's nodes do not replicate to each other. They share a store, and the
  store is the network. Killing a node and pausing a node are the faults
  that move membership, drop acknowledgements, and freeze a conditional
  write in mid-flight. A partition between nodes does not split that path.
  Partitioning a node from the store is `:partition`, and it is remote
  only: local processes share this machine's network stack, so the same
  iptables rule would also cut the client. The rule drops the store port,
  not every packet to that host, so SSH and the worker stay up. It is not
  part of the default suite. Run it against the nodes from `bin/lxc-up`.

  `:heal` resumes every node and starts any that are down. The generator
  runs it after the fault window, then waits, then the clients read."
  (:require [clojure.string :as str]
            [clojure.tools.logging :refer [info]]
            [jepsen.control :as c]
            [jepsen.echod.db :as db]
            [jepsen.nemesis :as nemesis]))

(def faults
  #{:kill :pause :partition})

(def fault-ops
  "The start and stop of one fault."
  {:kill [:kill :start]
   :pause [:pause :resume]
   :partition [:partition :unpartition]})

(defn store-host
  "The host a partition drops traffic to, from `--endpoint` or the store URL."
  [test]
  (or (:store-host test)
      (when-let [ep (:endpoint test)]
        (try (.getHost (java.net.URI. (str ep))) (catch Exception _ nil)))
      (when-let [s (:store-url test)]
        (when-not (str/starts-with? (str s) "file:")
          (try (.getHost (java.net.URI. (str s))) (catch Exception _ nil))))))

(defn store-port
  "TCP port of `--endpoint`, when the URI names one."
  [test]
  (when-let [ep (:endpoint test)]
    (try
      (let [p (.getPort (java.net.URI. (str ep)))]
        (when (pos? p) p))
      (catch Exception _ nil))))

(defn partition-args
  "iptables arguments that drop one node's TCP to the store. Naming the
  endpoint port keeps SSH and the worker up when the bucket shares a
  machine with the control host."
  [host port]
  (concat [:iptables :-A :OUTPUT :-p :tcp :-d (str host)]
          (when port [:--dport (str port)])
          [:-m :comment :--comment "echod-jepsen" :-j :DROP]))

(defn unpartition-args [host port]
  (assoc (vec (partition-args host port)) 1 :-D))

(defn- pick
  "Which nodes a fault hits. Two nodes have no minority that is smaller
  than a half, so one of them is the fault."
  [test target]
  (let [nodes (vec (:nodes test))
        n (count nodes)
        k (case target
            :one 1
            :all n
            :majority (max 1 (min n (+ 1 (quot (dec n) 2))))
            :minority (max 1 (min (dec n) (max 1 (quot (dec n) 2))))
            1)]
    (take (min k n) (shuffle nodes))))

(defn- on-nodes
  [test nodes f]
  (if (:local? test)
    (doseq [node nodes] (f test node))
    (c/on-nodes test nodes f)))

(defn- partition!
  [test nodes]
  (let [host (store-host test)]
    (when (:local? test)
      (throw (ex-info "partition is remote only: local nodes share the host network, so an iptables rule would also cut the client"
                      {})))
    (when (str/blank? host)
      (throw (ex-info "partition needs --endpoint or a store URL with a host" {})))
    (let [port (store-port test)]
      (c/on-nodes test nodes
                  (fn [_ _]
                    (c/su (apply c/exec (partition-args host port)))))
      {:partitioned (vec nodes) :from host :port port})))

(defn- unpartition!
  [test]
  (c/on-nodes test (:nodes test)
              (fn [_ _]
                (c/su (try (apply c/exec (unpartition-args (store-host test) (store-port test)))
                           (catch Exception _ :no-iptables)))))
  :unpartitioned)

(defrecord EchodNemesis [db target struck]
  nemesis/Nemesis
  (setup! [this _test] this)

  (invoke! [_ test op]
    (let [procs (:procs db)
          backing (:backing db)
          same (fn []
                 (let [prior (seq @struck)]
                   (if prior
                     (vec prior)
                     (vec (pick test target)))))
          fresh (fn []
                  (let [nodes (vec (pick test target))]
                    (reset! struck nodes)
                    nodes))]
      (try
        (case (:f op)
          :kill (let [nodes (fresh)]
                  (on-nodes test nodes (fn [_ node] (db/kill-node! test node procs)))
                  (assoc op :type :info :value [:killed nodes]))
          :start (let [nodes (same)]
                   (reset! struck nil)
                   (on-nodes test nodes (fn [_ node] (db/start-node! test node procs backing)))
                   (assoc op :type :info :value [:started nodes]))
          :pause (let [nodes (fresh)]
                   (on-nodes test nodes (fn [_ node] (db/pause-node! test node procs)))
                   (assoc op :type :info :value [:paused nodes]))
          :resume (let [nodes (same)]
                    (reset! struck nil)
                    (on-nodes test nodes (fn [_ node] (db/resume-node! test node procs)))
                    (assoc op :type :info :value [:resumed nodes]))
          :partition (let [nodes (fresh)]
                       (assoc op :type :info :value (partition! test nodes)))
          :unpartition (do (reset! struck nil)
                           (assoc op :type :info :value (unpartition! test)))
          :heal (do (reset! struck nil)
                    (db/heal! test (:nodes test) procs backing on-nodes)
                    (assoc op :type :info :value :healed))
          (assoc op :type :info :error (str "unknown nemesis op " (:f op))))
        (catch Exception e
          (info e "nemesis" (:f op))
          (assoc op :type :info :error (.getMessage e))))))

  (teardown! [_ test]
    (try (db/heal! test (:nodes test) (:procs db) (:backing db) on-nodes)
         (catch Exception e (info e "nemesis teardown")))))

(defn nemesis
  [opts]
  (map->EchodNemesis {:db (:db opts)
                      :target (:nemesis-target opts :minority)
                      :struck (atom nil)}))

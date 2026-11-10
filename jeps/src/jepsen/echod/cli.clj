(ns jepsen.echod.cli
  "A Jepsen test of echod from the outside.

  `lein run test --local` starts one process per node against one bucket
  (s3s-fs, when `--store` is omitted) and drives `POST /`. A pass is the
  checker saying the history that came back is a history of the document
  machine. `lein run test-all` is that test across the workloads and the
  kill and pause faults."
  (:gen-class)
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [jepsen.cli :as cli]
            [jepsen.client :as jc]
            [jepsen.control.sshj :as sshj]
            [jepsen.echod.db :as db]
            [jepsen.echod.nemesis :as nemesis]
            [jepsen.echod.workload :as workload]
            [jepsen.os :as os]
            [jepsen.tests :as tests]))

(defn parse-nemesis
  [s]
  (let [parts (->> (str/split (or s "") #",")
                   (map str/trim)
                   (remove #(or (str/blank? %) (#{"none" "nil"} %)))
                   (mapv keyword))
        bad (first (remove nemesis/faults parts))]
    (when bad
      (throw (IllegalArgumentException.
              (str "Unknown nemesis " bad ". Known: " (str/join ", " (map name nemesis/faults))))))
    parts))

(def extra-opts
  [   [nil "--local" "Run every node as a process on this machine. Without --store, starts s3s-fs. file:// cannot conditional-update, so it is refused."
    :default false]

   [nil "--bin PATH" "The echod binary."
    :default "../target/release/echod"]

   [nil "--store URL" "Bucket URL (s3://bucket). A local run with this omitted starts s3s-fs. file:// is refused: that backend cannot conditional-update."]

   [nil "--endpoint URL" "S3 endpoint, for a remote store or for --nemesis partition."]

   [nil "--region REGION" "S3 region."]

   [nil "--express" "The bucket is S3 Express: writes append."
    :default false]

   [nil "--prefix STRING" "Key prefix. Default is unique per test."]

   [nil "--workload NAME" "promise, task, idempotence, schedule, deadline, indefinite, or brutal."
    :default :promise
    :parse-fn keyword
    :validate [workload/workloads (cli/one-of workload/workloads)]]

   [nil "--nemesis FAULTS" "Comma-separated: none, kill, pause, partition. partition is remote only."
    :default []
    :parse-fn parse-nemesis]

   [nil "--nemesis-target TARGET" "one, minority, majority, or all."
    :default :minority
    :parse-fn keyword
    :validate [#{:one :minority :majority :all} (cli/one-of [:one :minority :majority :all])]]

   [nil "--client-nodes WHICH" "all: every request picks a node. one: a client stays on the node it opened."
    :default :all
    :parse-fn keyword
    :validate [#{:one :all} (cli/one-of [:one :all])]]

   [nil "--rate HZ" "Approximate operations per second, across the whole test."
    :default 30
    :parse-fn #(Double/parseDouble %)
    :validate [pos? "Must be positive"]]

   [nil "--key-count N" "Independent promises, or schedules."
    :default 40
    :parse-fn #(Long/parseLong %)
    :validate [pos? "Must be positive"]]

   [nil "--key-concurrency N" "Threads on one key. Concurrency is raised to a multiple of this."
    :default 2
    :parse-fn #(Long/parseLong %)
    :validate [pos? "Must be positive"]]

   [nil "--ops-per-key N" "Operations a key emits before its generator moves on, final read excluded."
    :default 20
    :parse-fn #(Long/parseLong %)
    :validate [pos? "Must be positive"]]

   [nil "--share N" "How many promise keys share one origin document."
    :default 4
    :parse-fn #(Long/parseLong %)
    :validate [pos? "Must be positive"]]

   [nil "--promise-timeout-ms MS" "Create timeout, as a deadline from now. An hour keeps timeouts out of the strict model."
    :default 3600000
    :parse-fn #(Long/parseLong %)
    :validate [pos? "Must be positive"]]

   [nil "--deadline-ms MS" "Create timeout for the deadline workload."
    :default 1500
    :parse-fn #(Long/parseLong %)
    :validate [pos? "Must be positive"]]

   [nil "--final-time-limit SECONDS" "How long the final reads may take."
    :default 30
    :parse-fn #(Long/parseLong %)
    :validate [pos? "Must be positive"]]

   [nil "--heal-time SECONDS" "After heal, how long to wait before the final reads."
    :default 8
    :parse-fn #(Long/parseLong %)
    :validate [#(not (neg? %)) "Must be non-negative"]]

   [nil "--initial-quiet-period SECONDS" "Client traffic before the first fault."
    :default 5
    :parse-fn #(Long/parseLong %)
    :validate [#(not (neg? %)) "Must be non-negative"]]

   [nil "--nemesis-interval SECONDS" "Pause between the two halves of a fault."
    :default 10
    :parse-fn #(Long/parseLong %)
    :validate [pos? "Must be positive"]]

   [nil "--heartbeat-ms MS" "How often a node refreshes its announcement."
    :default 500
    :parse-fn #(Long/parseLong %)]

   [nil "--node-ttl-ms MS" "An announcement older than this is a dead node."
    :default 2000
    :parse-fn #(Long/parseLong %)]

   [nil "--timer-bucket-ms MS" "Deadline bucket width. The deadline workload uses 400 unless this is set."
    :parse-fn #(Long/parseLong %)]

   [nil "--retry-timeout MS" "How long an unclaimed task waits before it is offered again."
    :default 60000
    :parse-fn #(Long/parseLong %)]

   [nil "--compact N" "Stale rows before a document is rewritten. 0 rewrites every write."
    :default 0
    :parse-fn #(Long/parseLong %)]

   [nil "--timeout MS" "Client timeout for one request. 503 and a timeout are :info."
    :default 5000
    :parse-fn #(Long/parseLong %)
    :validate [pos? "Must be positive"]]

   [nil "--final-timeout MS" "Client timeout for one attempt of a final read."
    :default 10000
    :parse-fn #(Long/parseLong %)
    :validate [pos? "Must be positive"]]

   [nil "--checker-timeout MS" "How long Knossos may spend on one key."
    :default 30000
    :parse-fn #(Long/parseLong %)
    :validate [pos? "Must be positive"]]

   [nil "--base-port PORT" "First local listen port. Node i listens on this plus i."
    :default 18001
    :parse-fn #(Long/parseLong %)]

   [nil "--port PORT" "Listen port on a remote node."
    :default 8001
    :parse-fn #(Long/parseLong %)]

   [nil "--worker-host HOST" "Host the nodes use to push execute and unblock. Local default is 127.0.0.1."
    :default "127.0.0.1"]

   [nil "--rust-log FILTER" "RUST_LOG for the nodes."
    :default "info"]

   [nil "--concurrency NUMBER" "Workers. A multiple of --key-concurrency; raised if it is not. Optionally ends in n."
    :default "2n"
    :validate [(partial re-find #"^\d+n?$")
               "Must be an integer, optionally followed by n."]]])

(defn align-concurrency
  "Knossos sees key-concurrency threads on a key, and the independent
  generator wants the test's concurrency to be a multiple of that."
  [opts]
  (let [kc (max 1 (long (:key-concurrency opts 2)))
        c (long (:concurrency opts))
        groups (max 1 (long (Math/ceil (/ (double c) kc))))]
    (assoc opts :key-concurrency kc :concurrency (* kc groups))))

(defn opt-fn
  [parsed]
  (let [opts (:options parsed)
        local? (:local opts)
        nemesis (:nemesis opts)]
    (when (and local? (some #{:partition} nemesis))
      (throw (IllegalArgumentException.
              "partition is remote only: local nodes share the host network, so an iptables rule would also cut the client. Use bin/lxc-up.")))
    (assoc parsed :options
           (-> opts
               (assoc :local? local?
                      :bin (.getCanonicalPath (io/file (:bin opts)))
                      :prefix (if (str/blank? (:prefix opts))
                                (str "jeps/" (System/currentTimeMillis) "-" (rand-int 1000000) "/")
                                (:prefix opts))
                      :ssh (cond-> (:ssh opts) local? (assoc :dummy? true)))
               align-concurrency))))

(defn echod-test
  [opts]
  (let [build (get workload/by-name (:workload opts))
        w (build opts)
        database (db/db)
        faults (vec (:nemesis opts))]
    (merge tests/noop-test
           {:name (str "echod-" (name (:workload opts))
                       (when (seq faults)
                         (str "-" (str/join "-" (map name faults)))))
            :nodes (:nodes opts)
            :ssh (:ssh opts)
            :argv (:argv opts)
            :remote (sshj/remote)
            :os os/noop
            :db database
            :client (jc/validate (:client w))
            :nemesis (nemesis/nemesis {:db database
                                       :nemesis-target (:nemesis-target opts :minority)})
            :generator (workload/generator opts (:client-gen w) (:final-gen w))
            :checker (:checker w)
            :local? (:local? opts)
            :bin (:bin opts)
            :store-url (:store opts)
            :endpoint (:endpoint opts)
            :region (:region opts)
            :express (:express opts)
            :prefix (:prefix opts)
            :compact (:compact opts)
            :heartbeat-ms (:heartbeat-ms opts)
            :node-ttl-ms (:node-ttl-ms opts)
            :timer-bucket-ms (or (:timer-bucket-ms opts)
                                 (:timer-bucket-ms w)
                                 3600000)
            :retry-timeout (:retry-timeout opts)
            :base-port (:base-port opts)
            :port (:port opts)
            :worker-host (:worker-host opts)
            :rust-log (:rust-log opts)
            :timeout (or (:client-timeout w) (:timeout opts))
            :final-timeout (:final-timeout opts)
            :client-nodes (:client-nodes opts)
            :nemesis-target (:nemesis-target opts)
            :concurrency (:concurrency opts)
            :time-limit (:time-limit opts)
            :nemesis-interval (:nemesis-interval opts)
            :share (:share opts)
            :key-count (:key-count opts)
            :key-concurrency (:key-concurrency opts)
            :ops-per-key (:ops-per-key opts)
            :rate (:rate opts)
            :promise-timeout-ms (:promise-timeout-ms opts)
            :deadline-ms (:deadline-ms opts)
            :final-time-limit (:final-time-limit opts)
            :heal-time (:heal-time opts)
            :initial-quiet-period (:initial-quiet-period opts)
            :checker-timeout (:checker-timeout opts)
            :workload (:workload opts)
            :nemesis-faults faults
            :leave-db-running? (:leave-db-running? opts)})))

(defn all-tests
  "The standard suite: each workload against no fault, kill, and pause."
  [opts]
  (for [w workload/suite-workloads
        faults [[] [:kill] [:pause]]]
    (echod-test (assoc opts :workload w :nemesis faults))))

(defn -main
  [& args]
  (cli/run!
   (merge (cli/single-test-cmd
           {:opt-spec extra-opts
            :opt-fn opt-fn
            :test-fn echod-test})
          (cli/test-all-cmd
           {:opt-spec extra-opts
            :opt-fn opt-fn
            :tests-fn all-tests})
          (cli/serve-cmd))
   args))

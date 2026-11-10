(ns jepsen.echod.db
  "Starts and stops echod.

  Local mode spawns one process per node on this machine. All of them are
  pointed at one bucket: the store is the network, which is how a real
  cluster is built. `file://` is not that bucket, because the local
  filesystem backend cannot conditional-update. With no `--store`, local
  mode starts s3s-fs. Remote mode uploads the binary and runs it over SSH
  against `--store`.

  The db does not open the store itself and does not speak the protocol.
  Ready means `GET /ready` returned 200. Logs stay under the test directory
  so the panic checker can read them after the processes are gone."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.tools.logging :refer [info warn]]
            [jepsen.control :as c]
            [jepsen.control.util :as cu]
            [jepsen.db :as db]
            [jepsen.echod.core :as core]
            [jepsen.echod.worker :as worker]
            [jepsen.store :as store])
  (:import (java.lang ProcessBuilder ProcessBuilder$Redirect)
           (java.net URI)
           (java.net.http HttpClient HttpRequest HttpResponse$BodyHandlers)
           (java.time Duration)
           (java.util.concurrent TimeUnit)))

(def remote-dir "/opt/echod")

(defn runtime-dir
  "Where this test's nodes write. A test that has not been run can pass
  `:runtime-dir` itself; a running test uses its store directory."
  [test]
  (io/file (or (:runtime-dir test)
               (.getPath (store/path test "runtime")))))

(defn node-dir
  [test node]
  (io/file (runtime-dir test) (str node)))

(defn log-file
  [test node]
  (io/file (node-dir test node) "echod.log"))

(defn store-dir
  [test]
  (io/file (runtime-dir test) "store"))

(defn file-store?
  "object_store's local filesystem does not implement conditional updates,
  so a `file://` bucket cannot commit a document."
  [url]
  (str/starts-with? (str url) "file:"))

(defn store-url
  "Where the nodes read and write. `:store` belongs to Jepsen's results.
  The bucket is `:store-url` (`--store`), or the s3s-fs this db started,
  recorded on `backing`."
  [test backing]
  (or (:store-url test)
      (:store-url @backing)
      (throw (ex-info "no store: pass --store, or run --local with s3s-fs installed"
                      {}))))

(defn- sh!
  [& args]
  (let [pb (ProcessBuilder. ^java.util.List (map str args))
        _ (.redirectErrorStream pb true)
        p (.start pb)
        out (slurp (.getInputStream p))
        exit (.waitFor p)]
    {:exit exit :out out}))

(defn- local-pid
  [procs node]
  (:pid (get @procs node)))

(defn- alive-pid?
  [pid]
  (and pid (zero? (:exit (sh! "kill" "-0" pid)))))

(defn alive?
  "Is this node's process still there? A paused process is alive."
  [test node procs]
  (if (:local? test)
    (alive-pid? (local-pid procs node))
    (try
      (let [pid (str/trim (str (c/exec :cat (str remote-dir "/echod.pid"))))]
        (c/exec :kill :-0 pid)
        true)
      (catch Exception _ false))))

(defn args
  "The flags for one node. One store, its own id and URL."
  [test node backing]
  (let [url (core/node-url test node)
        bind (if (:local? test)
               (str "127.0.0.1:" (core/node-port test node))
               (str "0.0.0.0:" (core/node-port test node)))
        endpoint (or (:endpoint test) (:endpoint @backing))
        region (or (:region test) (:region @backing))]
    (concat
     [(str (:bin test))
      "--store" (store-url test backing)
      "--bind" bind
      "--node-id" (str node)
      "--url" url
      "--prefix" (or (:prefix test) "")
      "--compact" (str (:compact test 0))
      "--heartbeat-ms" (str (:heartbeat-ms test 500))
      "--node-ttl-ms" (str (:node-ttl-ms test 2000))
      "--timer-bucket-ms" (str (:timer-bucket-ms test 3600000))
      "--retry-timeout" (str (:retry-timeout test 60000))]
     (when endpoint ["--endpoint" (str endpoint)])
     (when region ["--region" (str region)])
     (when (:express test) ["--express"]))))

(defn- tail
  [file n]
  (try
    (->> (slurp file)
         str/split-lines
         (take-last n)
         (str/join "\n"))
    (catch Exception _ "")))

(defn- wait-ready
  [url seconds]
  (let [client (-> (HttpClient/newBuilder)
                   (.connectTimeout (Duration/ofMillis 500))
                   .build)
        target (str url "ready")
        deadline (+ (System/currentTimeMillis) (* 1000 seconds))]
    (loop []
      (let [ok (try
                 (let [req (-> (HttpRequest/newBuilder)
                               (.uri (URI/create target))
                               (.timeout (Duration/ofMillis 500))
                               (.GET)
                               .build)
                       resp (.send client req (HttpResponse$BodyHandlers/discarding))]
                   (= 200 (.statusCode resp)))
                 (catch Exception _ false))]
        (cond
          ok true
          (< (System/currentTimeMillis) deadline)
          (do (Thread/sleep 200) (recur))
          :else false)))))

(defn- which
  "The first of `names` that is an executable on PATH or under Cargo's bin."
  [& names]
  (let [home (or (System/getenv "CARGO_HOME")
                 (str (System/getProperty "user.home") "/.cargo"))
        dirs (concat (str/split (or (System/getenv "PATH") "") #":")
                     [(str home "/bin")])]
    (first (for [d dirs
                 n names
                 :let [f (io/file d n)]
                 :when (and (.isFile f) (.canExecute f))]
             (.getAbsolutePath f)))))

(defn- port-open?
  [port]
  (try
    (with-open [_ (java.net.Socket. "127.0.0.1" (int port))]
      true)
    (catch Exception _ false)))

(defn- wait-port
  [port seconds]
  (let [deadline (+ (System/currentTimeMillis) (* 1000 seconds))]
    (loop []
      (cond
        (port-open? port) true
        (< (System/currentTimeMillis) deadline) (do (Thread/sleep 200) (recur))
        :else false))))

(defn- start-emulator!
  "s3s-fs on a directory of this test. `file://` cannot conditional-update,
  and the conditional commit is part of the pipeline a pass is about."
  [test backing]
  (let [bin (or (System/getenv "S3S_FS") (which "s3s-fs"))]
    (when-not bin
      (throw (ex-info (str "a local test needs a store that implements conditional updates. "
                           "file:// does not: LocalFileSystem has no PutMode::Update. "
                           "Install s3s-fs (`cargo install s3s-fs --features binary`) "
                           "or pass --store and --endpoint.")
                      {})))
    (let [port 18014
          root (io/file (runtime-dir test) "s3")
          log (io/file (runtime-dir test) "s3s.log")]
      (.mkdirs (io/file root "echod"))
      (let [cmd [bin "--host" "127.0.0.1" "--port" (str port)
                 "--access-key" "k" "--secret-key" "s"
                 (.getAbsolutePath root)]
            pb (ProcessBuilder. (into-array String cmd))]
        (.redirectErrorStream pb true)
        (.redirectOutput pb (ProcessBuilder$Redirect/appendTo log))
        (let [proc (.start pb)]
          (when-not (wait-port port 20)
            (.destroyForcibly proc)
            (throw (ex-info "s3s-fs never accepted connections" {:log (tail log 40)})))
          (reset! backing
                  {:proc proc
                   :store-url "s3://echod"
                   :endpoint (str "http://127.0.0.1:" port)
                   :region "us-east-1"
                   :env {"AWS_ACCESS_KEY_ID" "k"
                         "AWS_SECRET_ACCESS_KEY" "s"
                         "AWS_REGION" "us-east-1"
                         "AWS_EC2_METADATA_DISABLED" "true"}})
          (info "s3s-fs" (store-url test backing)))))))

(defn- stop-emulator!
  [backing]
  (when-let [proc (:proc @backing)]
    (.destroy proc)
    (when-not (.waitFor proc 3 TimeUnit/SECONDS)
      (.destroyForcibly proc))
    (reset! backing nil)))

(defn- prepare!
  [test backing]
  (let [bin (io/file (:bin test))]
    (when-not (.isFile bin)
      (throw (ex-info (str "echod binary not found: " bin
                           ". Build it with `cargo build --release -p echod` and pass --bin.")
                      {:bin (str bin)})))
    (when (file-store? (:store-url test))
      (throw (ex-info (str "file:// cannot hold a bucket: LocalFileSystem does not implement "
                           "conditional updates. Use s3:// with --endpoint, or omit --store "
                           "on a local run and let the test start s3s-fs.")
                      {:store (:store-url test)})))
    (.mkdirs (runtime-dir test))
    (when (and (:local? test) (str/blank? (:store-url test)))
      (start-emulator! test backing))
    (when (and (not (:local? test)) (str/blank? (:store-url test)))
      (throw (ex-info "a remote test needs --store" {:nodes (:nodes test)})))
    (worker/ensure-started! (or (:worker-host test) "127.0.0.1"))
    (worker/reset-inbox!)))

(defn- start-local!
  [test node procs backing]
  (let [dir (node-dir test node)
        log (log-file test node)
        cmd (mapv str (args test node backing))]
    (.mkdirs dir)
    (spit log (str "exec " (str/join " " cmd) "\n"))
    (let [pb (ProcessBuilder. (into-array String cmd))]
      (.directory pb dir)
      (.redirectErrorStream pb true)
      (.redirectOutput pb (ProcessBuilder$Redirect/appendTo log))
      (let [env (.environment pb)]
        (.put env "RUST_LOG" (or (:rust-log test) "info"))
        (doseq [[k v] (:env @backing)]
          (.put env (str k) (str v))))
      (let [proc (.start pb)
            pid (.pid proc)]
        (swap! procs assoc node {:pid pid :proc proc})
        (info "started" node "pid" pid)
        (when-not (wait-ready (core/node-url test node) 30)
          (throw (ex-info (str node " never became ready")
                          {:node node :log (tail log 40)})))))))

(defn- daemon-env
  "Environment for a remote echod. AWS credentials come from this process,
  so a bucket on s3s-fs authenticates the same way the control node does."
  [test]
  (into {"RUST_LOG" (or (:rust-log test) "info")}
        (keep (fn [k]
                (when-let [v (System/getenv k)]
                  (when-not (str/blank? v)
                    [k v])))
              ["AWS_ACCESS_KEY_ID"
               "AWS_SECRET_ACCESS_KEY"
               "AWS_SESSION_TOKEN"
               "AWS_REGION"
               "AWS_DEFAULT_REGION"
               "AWS_EC2_METADATA_DISABLED"])))

(defn- start-remote!
  [test node backing]
  (let [dir remote-dir
        bin (str dir "/echod")
        log (str dir "/echod.log")
        pidfile (str dir "/echod.pid")]
    (c/su
     (c/exec :mkdir :-p dir)
     (c/upload (:bin test) bin)
     (c/exec :chmod "755" bin)
     (apply cu/start-daemon!
            {:logfile log
             :pidfile pidfile
             :chdir dir
             :env (daemon-env test)}
            bin
            (rest (args test node backing))))
    (when-not (wait-ready (core/node-url test node) 40)
      (throw (ex-info (str node " never became ready") {:node node})))))

(declare stop-node!)

(defn start-node!
  [test node procs backing]
  (if (:local? test)
    (do (stop-node! test node procs)
        (start-local! test node procs backing))
    (start-remote! test node backing)))

(defn stop-node!
  [test node procs]
  (if (:local? test)
    (let [{:keys [pid proc]} (get @procs node)]
      (when proc
        (.destroy proc)
        (when-not (.waitFor proc 3 TimeUnit/SECONDS)
          (.destroyForcibly proc)
          (.waitFor proc 2 TimeUnit/SECONDS)))
      (when (alive-pid? pid)
        (sh! "kill" "-KILL" pid))
      (swap! procs dissoc node))
    (c/su (cu/stop-daemon! (str remote-dir "/echod.pid")))))

(defn kill-node!
  [test node procs]
  (if (:local? test)
    (let [{:keys [pid proc]} (get @procs node)]
      (when (alive-pid? pid) (sh! "kill" "-KILL" pid))
      (when proc (.destroyForcibly proc))
      (swap! procs dissoc node)
      :killed)
    (do (c/su (cu/stop-daemon! (str remote-dir "/echod.pid")))
        :killed)))

(defn- signal-local!
  [procs node sig]
  (when-let [pid (local-pid procs node)]
    (when (alive-pid? pid)
      (sh! "kill" (str "-" sig) pid))))

(defn pause-node!
  [test node procs]
  (if (:local? test)
    (do (signal-local! procs node "STOP") :paused)
    (let [pid (str/trim (str (c/exec :cat (str remote-dir "/echod.pid"))))]
      (c/su (c/exec :kill :-STOP pid))
      :paused)))

(defn resume-node!
  [test node procs]
  (if (:local? test)
    (do (signal-local! procs node "CONT") :resumed)
    (try
      (let [pid (str/trim (str (c/exec :cat (str remote-dir "/echod.pid"))))]
        (c/su (c/exec :kill :-CONT pid))
        :resumed)
      (catch Exception _ :not-running))))

(defn clear-partition!
  "Drop any store-port rule a previous fault left in OUTPUT. A fault window
  can end while a node is still cut, and the next test would then start
  unable to reach the bucket."
  [test]
  (when-not (:local? test)
    (try (c/su (c/exec :iptables :-F :OUTPUT))
         (catch Exception _ nil))))

(defn heal!
  "Resume anything frozen and start anything that is not running. `on` is
  `jepsen.control/on-nodes` for a remote test and a local loop otherwise;
  the nemesis supplies it so a remote call happens on that node."
  [test nodes procs backing on]
  (on test nodes
      (fn [test node]
        (try (clear-partition! test)
             (catch Exception e (warn e "clear partition" node)))
        (try (resume-node! test node procs)
             (catch Exception e (warn e "resume" node)))
        (when-not (try (alive? test node procs) (catch Exception _ false))
          (try (start-node! test node procs backing)
               (catch Exception e (warn e "restart" node)))))))

(defrecord DB [procs prepared? backing]
  db/DB
  (setup! [_ test node]
    (try (clear-partition! test) (catch Exception _ nil))
    (locking prepared?
      (when (compare-and-set! prepared? false true)
        (prepare! test backing)))
    (start-node! test node procs backing))

  (teardown! [_ test node]
    (when-not (:leave-db-running? test)
      (try (stop-node! test node procs)
           (catch Exception e (warn e "stop" node))))
    (when (= node (last (:nodes test)))
      (reset! prepared? false)
      (when-not (:leave-db-running? test)
        (stop-emulator! backing)
        (worker/stop!))))

  db/LogFiles
  (log-files [_ test _node]
    (if (:local? test)
      {}
      {(str remote-dir "/echod.log") "echod.log"}))

  db/Kill
  (kill! [_ test node] (kill-node! test node procs))
  (start! [_ test node] (start-node! test node procs backing))

  db/Pause
  (pause! [_ test node] (pause-node! test node procs))
  (resume! [_ test node] (resume-node! test node procs)))

(defn db
  []
  (DB. (atom {}) (atom false) (atom nil)))

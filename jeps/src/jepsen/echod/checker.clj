(ns jepsen.echod.checker
  "What a pass means.

  For the promise, task, idempotence, and indefinite workloads, Knossos has
  found a linearization of every key against the document machine. The
  history was produced by HTTP against the nodes, so that linearization is
  the gateway, admission, the process, the conditional commit, and the codec
  agreeing with the machine. `:unknown` — the search ran out of time, or a
  final read never returned — is not a pass.

  The deadline workload is not that search. A timeout is a transition no
  client invoked, so the checker is the one a reader can check by hand: one
  terminal state, a timer resolves, a non-timer does not resolve empty, and
  the final read is terminal.

  Invariants are the same facts written out, so a failure names the promise
  and the two reads that disagree instead of a Knossos config."
  (:require [clojure.string :as str]
            [jepsen.checker :as checker]
            [jepsen.echod.core :as c]
            [jepsen.echod.db :as db]
            [jepsen.echod.worker :as worker]
            [jepsen.independent :as independent]
            [knossos.linear :as linear]))

(def linear-claim
  "A pass means every key's history is linearizable against the document machine. The gateway, admission, the process, the conditional commit, and the codec produced a correct result. This is an outside oracle, not a proof. :unknown means the search did not finish or a final read did not return; it is not a pass.")

(def deadline-claim
  "A pass means every created promise was observed in one terminal state, a timer resolved instead of timing out, a non-timer did not resolve with an empty value, and the final read was terminal. A timeout is a transition nobody invoked, so this workload is not a Knossos linearization. It is an outside oracle, not a proof.")

(defn- plain
  [op]
  {:index (:index op)
   :time (:time op)
   :type (:type op)
   :process (:process op)
   :f (:f op)
   :value (:value op)
   :error (:error op)})

(defn client-ops
  "Client operations as plain maps. Nemesis, log, and sleep operations are
  copied into every per-key history; Knossos does not want them."
  [history]
  (mapv plain
        (filter (fn [op]
                  (and (integer? (:process op))
                       (#{:invoke :ok :info :fail} (:type op))))
                history)))

(defn explode-infos
  "Knossos 0.3.10 does not free a process when its call completes `:info`,
  and the next invoke of that process is rejected. The crashed call has to
  stay pending — it may or may not have happened — so the invoke and its
  `:info` move to a process of their own. Later calls of the real process
  stay on it, and the search still tries the crashed call both ways."
  [ops]
  (let [n (atom 1000000)]
    (loop [ops (seq ops)
           open {}
           out []]
      (if-let [op (first ops)]
        (case (:type op)
          :invoke
          (recur (next ops) (assoc open (:process op) (count out)) (conj out op))

          :info
          (if-let [i (get open (:process op))]
            (let [p (swap! n inc)]
              (recur (next ops)
                     (dissoc open (:process op))
                     (-> out
                         (assoc i (assoc (nth out i) :process p))
                         (conj (assoc op :process p)))))
            (recur (next ops) open (conj out op)))

          (:ok :fail)
          (recur (next ops) (dissoc open (:process op)) (conj out op))

          (recur (next ops) open out))
        out))))

(defn bounded-linear
  "Linearizability of one key, giving up after `timeout-ms`. A search that
  does not finish is `:unknown`."
  [model timeout-ms]
  (reify checker/Checker
    (check [_ _test history _opts]
      (let [ops (explode-infos (client-ops history))]
        (try
          (let [r (linear/analysis model ops {:time-limit timeout-ms})]
            {:valid? (:valid? r)
             :analyzer (:analyzer r)
             :op (:op r)
             :last-op (:last-op r)
             :previous-ok (:previous-ok r)
             :error (:msg r)
             :cause (:cause r)})
          (catch Exception e
            {:valid? :unknown
             :error (.getMessage e)}))))))

(defn- envelope-error
  [op]
  (let [v (:value op)]
    (cond
      (not (map? v)) "response is not a record"
      (not= (:http v) (:status v)) (str "HTTP " (:http v) " is not the envelope status " (:status v))
      (c/blank? (:node v)) "response has no x-echod-node header"
      :else nil)))

(defn- promise-snap
  "A 200 that carried a promise, or a 404."
  [op]
  (let [v (:value op)]
    (cond
      (and (= 200 (:status v)) (:promise v))
      (assoc (:promise v) :f (:f op) :pos (:pos op) :final? (:final? v))

      (= 404 (:status v))
      {:absent? true :f (:f op) :pos (:pos op) :final? (:final? v)}

      :else nil)))

(defn- pairs
  "Completed `:ok` calls in history order, each with its invoke."
  [ops]
  (loop [ops ops
         i 0
         open {}
         out []]
    (if-let [op (first ops)]
      (let [op (assoc op :pos i)
            p (:process op)]
        (case (:type op)
          :invoke (recur (next ops) (inc i) (assoc open p op) out)
          :ok (recur (next ops) (inc i) (dissoc open p)
                     (if-let [inv (get open p)]
                       (conj out {:invoke inv :ok op})
                       out))
          (recur (next ops) (inc i) (dissoc open p) out)))
      out)))

(defn- precedes?
  "A finished before B started. The history is in real time."
  [a b]
  (< (:pos (:ok a)) (:pos (:invoke b))))

(defn- identity-error
  [snaps]
  (let [present (remove :absent? snaps)
        fields (fn [s] (select-keys s [:param :timeout-at :tags :created-at]))
        got (distinct (map fields present))]
    (when (> (count got) 1)
      {:error "a promise's identity changed"
       :saw (vec (take 4 got))})))

(defn- terminal-error
  [snaps]
  (let [terms (->> snaps
                   (remove :absent?)
                   (remove #(= "pending" (:state %)))
                   (map #(select-keys % [:state :value]))
                   distinct)]
    (when (> (count terms) 1)
      {:error "a promise had more than one terminal state"
       :saw (vec terms)})))

(defn- realtime-error
  [paired]
  (let [snap (fn [pair]
               (promise-snap (:ok pair)))]
    (some (fn [a]
            (some (fn [b]
                    (when (precedes? a b)
                      (let [sa (snap a)
                            sb (snap b)]
                        (cond
                          (and sa (not (:absent? sa)) sb (:absent? sb))
                          {:error "a later read missed a promise an earlier read had found"
                           :earlier (dissoc sa :tags)
                           :later (dissoc sb :tags)}

                          (and sa (not (:absent? sa)) (not= "pending" (:state sa))
                               sb (not (:absent? sb))
                               (not= (select-keys sa [:state :value])
                                     (select-keys sb [:state :value])))
                          {:error "a terminal promise changed after it was observed"
                           :earlier (select-keys sa [:state :value])
                           :later (select-keys sb [:state :value])}

                          :else nil))))
                  paired))
          paired)))

(defn- task-error
  [paired]
  (let [task (fn [pair]
               (let [v (:value (:ok pair))]
                 (when (and (= 200 (:status v)) (:task v))
                   (:task v))))]
    (some (fn [a]
            (when-let [ta (task a)]
              (some (fn [b]
                      (when (precedes? a b)
                        (when-let [tb (task b)]
                          (cond
                            (and (:version ta) (:version tb)
                                 (> (long (:version ta)) (long (:version tb))))
                            {:error "a task version went backwards"
                             :earlier (:version ta)
                             :later (:version tb)}

                            (and (= "fulfilled" (:state ta))
                                 (not= "fulfilled" (:state tb)))
                            {:error "a fulfilled task left that state"
                             :later (:state tb)}

                            :else nil))))
                    paired)))
          paired)))

(defn invariants
  "The promise facts a reader can check without Knossos: the two copies of
  the status agree, the promise keeps its identity, it has one terminal
  state, and a terminal read is never followed by a different one."
  []
  (reify checker/Checker
    (check [_ _test history _opts]
      (let [ops (client-ops history)
            oks (filter #(= :ok (:type %)) ops)
            env (some envelope-error oks)
            paired (pairs ops)
            snaps (keep promise-snap (map :ok paired))
            bad (or (when env {:error env})
                    (identity-error snaps)
                    (terminal-error snaps)
                    (realtime-error paired)
                    (task-error paired))]
        (if bad
          (assoc bad :valid? false)
          {:valid? true
           :reads (count snaps)})))))

(defn schedule-invariants
  "A yearly schedule does not fire during the test. A fire is `lastRunAt`."
  []
  (reify checker/Checker
    (check [_ _test history _opts]
      (let [ops (client-ops history)
            oks (filter #(= :ok (:type %)) ops)
            env (some envelope-error oks)
            fired (filter (fn [op]
                            (some? (:last-run-at (:schedule (:value op)))))
                          oks)]
        (cond
          env {:valid? false :error env}
          (seq fired) {:valid? false
                       :error "a schedule fired during the strict schedule test"
                       :example (:schedule (:value (first fired)))}
          :else {:valid? true})))))

(defn- timer-request?
  [ops]
  (some (fn [op]
          (and (= :invoke (:type op))
               (= :create (:f op))
               (c/timer? (:value op))))
        ops))

(defn- created-ok?
  [ops]
  (some (fn [op]
          (and (= :ok (:type op))
               (= :create (:f op))
               (= 200 (:status (:value op)))))
        ops))

(defn check-deadline
  "One key of the deadline workload."
  [ops]
  (let [ops (map-indexed (fn [i op] (assoc op :pos i)) (client-ops ops))
        oks (filterv #(= :ok (:type %)) ops)
        env (some envelope-error oks)
        timer (timer-request? ops)
        created (created-ok? ops)
        paired (pairs ops)
        snaps (keep promise-snap oks)
        finals (->> ops
                    (filter #(and (= :get (:f %)) (:final? (:value %))))
                    (filter #(#{:ok :info} (:type %))))
        final (last finals)
        present (remove :absent? snaps)
        illegal (some (fn [s]
                        (cond
                          (and timer (= "rejected_timedout" (:state s)))
                          "a timer timed out as rejected_timedout"

                          (and (not timer) (= "resolved" (:state s)) (nil? (:value s)))
                          "a non-timer promise resolved with an empty value"

                          :else nil))
                      present)]
    (cond
      env
      {:valid? false :error env}

      (and (seq finals) (not= :ok (:type final)))
      {:valid? :unknown :error "the final read did not complete"}

      (and final (= :ok (:type final)) (= 404 (:status (:value final))) created)
      {:valid? false :error "the final read lost a promise that was created"}

      (and final (= :ok (:type final))
           (= 200 (:status (:value final)))
           (= "pending" (:state (:promise (:value final)))))
      {:valid? false :error "the deadline never fired; the final read is still pending"}

      illegal
      {:valid? false :error illegal}

      :else
      (if-let [bad (or (identity-error snaps)
                       (terminal-error snaps)
                       (realtime-error paired))]
        (assoc bad :valid? false)
        {:valid? true :timer timer}))))

(defn deadline
  []
  (reify checker/Checker
    (check [_ _test history _opts]
      (check-deadline history))))

(defn exercised
  "The workload actually drew a successful answer for each of `fs`. A
  history of only crashes is not a pass, and neither is a linearization of
  nothing."
  [fs]
  (reify checker/Checker
    (check [_ _test history _opts]
      (let [ok-fs (->> (client-ops history)
                       (filter #(= :ok (:type %)))
                       (filter #(let [s (:status (c/value-of %))]
                                  (and (number? s) (<= 200 s 299))))
                       (map :f)
                       set)
            missing (vec (remove ok-fs fs))]
        (if (seq missing)
          {:valid? false :missing missing :ok (vec (sort ok-fs))}
          {:valid? true :ok (vec (sort ok-fs))})))))

(defn stats
  "Counts, without the stock stats checker's rule that an `:f` with no
  `:ok` makes the whole test `:unknown`. `exercised` is that rule, and it
  names the functions it wanted."
  []
  (reify checker/Checker
    (check [_ _test history _opts]
      (let [ops (client-ops history)
            done (remove #(= :invoke (:type %)) ops)
            by (group-by :f done)
            row (fn [fs]
                  (let [n (group-by :type fs)]
                    {:ok (count (:ok n))
                     :info (count (:info n))
                     :fail (count (:fail n))}))]
        {:valid? true
         :count (count done)
         :by-f (into (sorted-map) (map (fn [[f fs]] [f (row fs)]) by))}))))

(defn check-unblocks
  "At most one unblock per promise, and its state is the terminal state a
  read observed when a read observed one. A missing unblock is delivery
  being at most once, which is not a failure. A repeated execute is a
  retry, which is not a failure either."
  [unblocks executes ops]
  (let [by (group-by :id unblocks)
        dups (->> by (filter #(> (count (val %)) 1)) (map key) vec)
        pending (->> unblocks (filter #(= "pending" (:state %))) (map :id) vec)
        observed (reduce (fn [m op]
                           (let [v (c/value-of op)
                                 p (:promise v)]
                             (if (and (= :ok (:type op)) p (= 200 (:status v))
                                      (not= "pending" (:state p)))
                               (update m (:id p) (fnil conj []) (:state p))
                               m)))
                         {}
                         ops)
        mismatch (vec
                  (for [[id us] by
                        :let [want (distinct (get observed id))
                              got (distinct (map :state us))]
                        :when (and (seq want)
                                   (not= (set want) (set got)))]
                    {:id id :unblock got :observed want}))]
    (cond
      (seq dups) {:valid? false :error "a listener was notified more than once" :ids dups}
      (seq pending) {:valid? false :error "an unblock carried a pending promise" :ids pending}
      (seq mismatch) {:valid? false :error "an unblock disagreed with a read" :examples mismatch}
      :else {:valid? true
             :unblocks (count unblocks)
             :executes (count executes)})))

(defn push
  []
  (reify checker/Checker
    (check [_ _test history _opts]
      (check-unblocks (worker/unblocks) (worker/executes) history))))

(defn panic
  "A Rust panic in a node log is a crash the model never sees, because the
  process is gone and the call comes back as `:info`."
  []
  (reify checker/Checker
    (check [_ test _history _opts]
      (let [dir (db/runtime-dir test)
            files (when (and dir (.isDirectory dir))
                    (filter #(.isFile %) (file-seq dir)))
            hits (for [f files
                       :let [lines (try (str/split-lines (slurp f))
                                        (catch Exception _ nil))]
                       line lines
                       :when (str/includes? line "panicked at")]
                   {:file (str f) :line line})]
        (if (seq hits)
          {:valid? false :panics (vec (take 5 hits))}
          {:valid? true})))))

(defn claim
  [text]
  (reify checker/Checker
    (check [_ _ _ _]
      {:valid? true :text text})))

(defn suite
  "The checkers for one workload.

  `:model`     a Knossos model, or nil for the deadline workload.
  `:deadline?` the deadline checker instead of the model.
  `:schedule?` schedule invariants instead of promise invariants.
  `:required`  functions that must have drawn a 2xx.
  `:claim`     the sentence a pass is allowed to mean."
  [{:keys [model deadline? schedule? required claim-text timeout-ms]}]
  (let [per-key (cond
                  deadline? (deadline)
                  model (checker/compose
                         {:linear (bounded-linear model (long (or timeout-ms 30000)))
                          :invariants (if schedule?
                                        (schedule-invariants)
                                        (invariants))})
                  :else (checker/unbridled-optimism))]
    (checker/compose
     {:keys (independent/checker per-key)
      :exercised (exercised (or required []))
      :push (push)
      :panic (panic)
      :stats (stats)
      :exceptions (checker/unhandled-exceptions)
      :claim (claim (or claim-text linear-claim))})))

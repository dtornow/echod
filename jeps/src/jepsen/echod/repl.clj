(ns jepsen.echod.repl
  "A few names for a REPL after a run. `(latest)` is the most recent test."
  (:require [jepsen.store :as store]))

(defn latest
  []
  (store/test -1))

(defn history
  []
  (:history (latest)))

(defn results
  []
  (:results (latest)))

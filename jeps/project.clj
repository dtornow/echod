(defproject jepsen.echod "0.1.0-SNAPSHOT"
  :description "Jepsen tests for echod. A pass means the pipeline a client can see — HTTP, admission, the process, the conditional commit, the codec — produced a correct result."
  :url "https://github.com/dtornow/echod"
  :license {:name "Apache-2.0"
            :url "https://www.apache.org/licenses/LICENSE-2.0"}
  :dependencies [[cheshire "5.13.0"]
                 [jepsen "0.3.5"]
                 [org.clojure/clojure "1.11.1"]]
  :repl-options {:init-ns jepsen.echod.repl}
  :main jepsen.echod.cli
  :jvm-opts ["-server"
             "-Xmx4g"
             "-Djava.awt.headless=true"]
  :test-selectors {:default (fn [m] (not (:integration m)))
                   :all (fn [m] true)
                   :focus :focus
                   :integration :integration}
  :profiles {:dev {:dependencies [[org.clojure/test.check "1.1.1"]]}})

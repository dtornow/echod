import Experiment.Promise
import Experiment.Fuzz

/-!
# One service, three shells

The promise handlers, unchanged, run sequentially, concurrently, and under
a fuzzer.
-/

namespace Experiment

def req (a : Addr) (id : CallId) (r : Request) : Input Msg := .msg a (.req id r)

def timedOut : Record := ⟨"p", .rejectedTimedout, "", 10⟩
def pending (t : Time) : Record := ⟨"p", .pending, "", t⟩

/-! ## Sequential

`c` creates `p` with a timeout at 10; `w` listens; `c` reads at 5 and at
20; `c` tries to settle at 21. -/

def scenario : List (Time × Input Msg) :=
  [(0, req "c" 1 (.create "p" (some 10))), (1, req "w" 2 (.listen "p" "w")),
   (5, req "c" 3 (.get "p")), (20, req "c" 4 (.get "p")),
   (21, req "c" 5 (.settle "p" .resolved "v"))]

def seqOuts (cfg : Config) (ins : List (Time × Input Msg)) : List (List (Out Msg)) :=
  (runs promises cfg {} ins).map (·.2)

-- No choices: one run.
#guard (seqOuts {} scenario).length == 1
#guard (seqOuts {} scenario).map sends ==
  [[("c", .res 1 ⟨200, some (pending 10)⟩), ("w", .res 2 ⟨200, some (pending 10)⟩),
    ("c", .res 3 ⟨200, some (pending 10)⟩),
    ("w", .notify timedOut), ("c", .res 4 ⟨200, some timedOut⟩),     -- the read at 20 times it out
    ("c", .res 5 ⟨200, some timedOut⟩)]]
#guard (seqOuts {} scenario).map hit == [["settle arrives after the timeout"]]
#guard (seqOuts {} scenario).all (failed · == [])
-- Without a read, a tick does it, once.
#guard (seqOuts {} [(0, req "c" 1 (.create "p" (some 10))), (1, req "w" 2 (.listen "p" "w")),
    (20, .tick), (30, .tick)]).map (fun o => (sends o).filter (·.1 == "w")) ==
  [[("w", .res 2 ⟨200, some (pending 10)⟩), ("w", .notify timedOut)]]
-- The default timeout is configuration.
#guard (seqOuts { defaultTimeout := 5 } [(0, req "c" 1 (.create "p" none))]).map sends ==
  [[("c", .res 1 ⟨200, some (pending 5)⟩)]]
-- Failure is a choice: every request may be answered 503, done or not.
-- Three requests, 27 runs; in one of them all three are shed and `p` was never made.
#guard (seqOuts { unreliable := true } (scenario.take 3)).length == 27
#guard (seqOuts { unreliable := true } (scenario.take 3)).any fun o =>
  sends o == [("c", .res 1 ⟨503, none⟩), ("w", .res 2 ⟨503, none⟩), ("c", .res 3 ⟨503, none⟩)]

/-! ## Concurrent

`a` creates `p` while `b` reads it. The network delivers `b`'s read first:
`b` sees 404. The server's inputs, in the order it took them, are a
sequential run sending exactly what it sent (`server_seq`, checked here
by running the sequential shell). -/

def race : List (Time × Act Msg) :=
  [(0, .request "a" (.req 1 (.create "p" (some 10)))),
   (0, .request "b" (.req 2 (.get "p"))),
   (1, .deliver 1),        -- the server takes b's read
   (1, .deliver 0),        -- then a's create
   (2, .deliver 0),        -- b receives its answer
   (2, .deliver 0)]        -- a receives its answer

def raceRun : Execution promises := (schedule promises {} {} race).getD []

#guard raceRun.length == 6
#guard (raceRun.map (·.1)).drop 4 ==
  [(.client "b", 2, .receive .server (.res 2 ⟨404, none⟩)),
   (.client "a", 2, .receive .server (.res 1 ⟨200, some (pending 10)⟩))]
#guard serverInputs raceRun == [(1, req "b" 2 (.get "p")), (1, req "a" 1 (.create "p" (some 10)))]
#guard (runs promises {} {} (serverInputs raceRun)).any fun r => sends r.2 == serverSends raceRun
-- The server takes no message twice: delivering a fifth time is impossible.
#guard (schedule promises {} {} (race ++ [(3, .deliver 0)])).isNone

/-! ## Fuzzing

Two hundred random runs of twelve steps, with failures on. No
`always` fails, every `sometimes` is hit, and in every run the sequential
shell explains the server. -/

def inputs : List (Addr × Msg) :=
  [("a", .req 1 (.create "p" (some 10))), ("a", .req 2 (.get "p")),
   ("w", .req 3 (.listen "p" "w")), ("b", .req 4 (.settle "p" .resolved "v")),
   ("b", .req 5 (.settle "p" .pending ""))]

def fuzzRuns : List (Execution promises) :=
  (List.range 200).map fun seed => fuzz promises { unreliable := true } {} inputs seed 12

#guard fuzzRuns.all fun x => failed (outs x) == []
#guard ["create finds the promise settled", "settle arrives after the timeout"].all fun n =>
  fuzzRuns.any fun x => (hit (outs x)).contains n
#guard fuzzRuns.all fun x =>
  (runs promises { unreliable := true } {} (serverInputs x)).any fun r => sends r.2 == serverSends x

end Experiment

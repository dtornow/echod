import «valid».«lean».intervals

/-! Local benchmark harness: one workload, one size per process, so peak memory
    is per case. The scripts are `valid/lean/experiments.lean`'s, with the
    awaited/targeted promise deadline pushed far out so long runs stay live. -/

namespace Bench

open ServerModel AbstractModel Abstraction Equivalence TraceCheck TraceCheck.Intervals

def ext : Tags := [("resonate:external", "true")]
def tgt : Tags := [("resonate:target", "w1")]
def far : Nat := 100000

def workflow (i : Nat) (t0 t1 : Nat) : List (Step × Nat) :=
  let a := oid s!"a{i}"
  let x := oid s!"x{i}"
  [ (.external (.promiseCreate { id := a, timeoutAt := far, param := {}, tags := ext }), t0)
  , (.external (.promiseCreate { id := x, timeoutAt := far, param := {}, tags := tgt }), t0)
  , (.external (.taskAcquire   { id := x, version := 0, pid := "p", ttl := 50 }), t0)
  , (.external (.taskSuspend   { id := x, version := 1, actions := [{ awaited := a, awaiter := x }] }), t0)
  , (.external (.promiseSettle { id := a, state := .resolved, value := {} }), t1)
  , (.internal (.callback { awaited := a, awaiter := x }), t1)
  , (.external (.taskAcquire   { id := x, version := 1, pid := "p", ttl := 50 }), t1)
  , (.external (.taskFulfill { id := x, version := 2, action := { id := x, state := .resolved, value := {} } }), t1) ]

def lengthScript (k : Nat) : List (Step × Nat) :=
  (List.range k).flatMap fun i => workflow i (10 + i * 10) (15 + i * 10)

def fanoutScript (n : Nat) : List (Step × Nat) :=
  (List.range n).map (fun i =>
      (.external (.promiseCreate { id := oid s!"a{i}", timeoutAt := 20 + i, param := {}, tags := ext }), 10))
  ++ [ (.external (.promiseGet { id := oid "a0" }), 500) ]

end Bench

open Bench TraceCheck TraceCheck.Intervals in
def main (args : List String) : IO Unit := do
  let kind := args.headD "length"
  for n in (args.drop 1).map String.toNat! do
    let (script, coned) := match kind with
      | "fanout" => (fanoutScript n, true)
      | "fanout-nocone" => (fanoutScript n, false)
      | _ => (lengthScript n, true)
    let trace := recordFrom script
    let t0 ← IO.monoNanosNow
    let v := validateBy false coned trace 16 10000000
    let line := verdictLine v
    if line.length == 0 then IO.eprintln "" else pure ()
    let t1 ← IO.monoNanosNow
    IO.println s!"{kind} n={n} events={trace.length} {line} {(t1 - t0).toFloat / 1000000.0}ms"

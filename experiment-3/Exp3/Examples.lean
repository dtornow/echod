import Exp3.Node

/-!
# Runs

Experiment 2's scenarios, and one it could not have: one node serving two
requests at once.
-/

namespace Exp3

open Experiment (Time Addr Request Response Msg CallId)
open Experiment.Storage (CMsg Config)

inductive Script where
  | send (a to : Addr) (m : Msg)
  | move (from_ to : Addr) (j : Nat := 0)

def drive (cfg : Config) (script : List (Time × Script)) : Option (Experiment.Network.Execution system) :=
  let rec go (c : Experiment.Network.Conf system) :
      List (Time × Script) → Option (Experiment.Network.Execution system)
    | [] => some []
    | (t, s) :: rest => do
      let act ← match s with
        | .send a to m => some (Experiment.Network.Act.request a to (.app m))
        | .move f to j =>
          (c.net.findIdx? fun (w, w', _) => w.addr == f && w'.addr == to).map
            (fun i => Experiment.Network.Act.deliver i j)
      let (l, o, c') ← c.take cfg t act
      let x ← go c' rest
      return (l, o, c') :: x
  go (Experiment.Network.initial world) script

def answerTo (a : Addr) (x : Experiment.Network.Execution system) : List Msg :=
  x.filterMap fun ((w, _, ev), _, _) =>
    match w, ev with
    | .client b, .receive _ (.app m) => if a == b then some m else none
    | _, _ => none

/-- The clients that were answered, in order. -/
def answered (x : Experiment.Network.Execution system) : List Addr :=
  x.filterMap fun ((w, _, ev), _, _) =>
    match w, ev with
    | .client b, .receive _ _ => some b
    | _, _ => none

def through (a n : Addr) (id : Nat) (r : Request) (t : Time) : List (Time × Script) :=
  [(t, .send a n (.req id t r)), (t, .move a n), (t, .move n "s3"), (t, .move "s3" n),
   (t, .move n "s3"), (t, .move "s3" n), (t, .move n a)]

def settled (v : String) (st : Experiment.PromiseState) : Response := ⟨200, some ⟨"p", st, v, 100⟩⟩

/-! ## Two settles racing on two nodes -/

def race : List (Time × Script) :=
  through "c" "n1" 1 (.create "p" (some 100)) 0 ++
  [(1, .send "a" "n1" (.req 2 1 (.settle "p" .resolved "x"))),
   (1, .send "b" "n2" (.req 3 1 (.settle "p" .rejected "y"))),
   (1, .move "a" "n1"), (1, .move "b" "n2"),
   (1, .move "n1" "s3"), (1, .move "n2" "s3"),
   (1, .move "s3" "n1"), (1, .move "s3" "n2"),
   (1, .move "n1" "s3"), (1, .move "s3" "n1"),
   (1, .move "n2" "s3"), (1, .move "s3" "n2")]

def safe := (drive {} (race ++ [(1, .move "n2" "s3"), (1, .move "s3" "n2"),
  (2, .move "n1" "a"), (2, .move "n2" "b")])).getD []

#guard safe.length == 23
#guard answerTo "a" safe == [.res 2 (settled "x" .resolved)]
#guard answerTo "b" safe == [.res 3 (settled "x" .resolved)]
#guard refines {} safe

def lost := (drive { conditional := false } (race ++ [(2, .move "n1" "a"), (2, .move "n2" "b")])).getD []

#guard answerTo "b" lost == [.res 3 (settled "y" .rejected)]
#guard !refines { conditional := false } lost

/-! ## Two requests in flight on one node

`a` creates `p` and `b` reads `q`, both through `n1`. Both loads go out at
once; `b`'s read is answered while `a`'s write is still on its way. -/

def both := (drive {}
  [(0, .send "a" "n1" (.req 1 0 (.create "p" (some 100)))), (0, .move "a" "n1"),
   (0, .send "b" "n1" (.req 2 0 (.get "q"))), (0, .move "b" "n1"),
   (0, .move "n1" "s3"), (0, .move "n1" "s3"),       -- both loads at the store
   (0, .move "s3" "n1"), (0, .move "s3" "n1"),       -- p loaded: write; q loaded: answer
   (0, .move "n1" "b"),
   (0, .move "n1" "s3"), (0, .move "s3" "n1"), (0, .move "n1" "a")]).getD []

#guard both.length == 12
#guard answered both == ["b", "a"]
#guard answerTo "b" both == [.res 2 ⟨404, none⟩]
#guard answerTo "a" both == [.res 1 ⟨200, some ⟨"p", .pending, "", 100⟩⟩]
#guard refines {} both

/-! ## Fuzzing, a little -/

def inputs : List (Addr × CMsg) :=
  [("a", .app (.req 1 0 (.create "p" (some 10)))), ("a", .app (.req 2 0 (.get "p"))),
   ("b", .app (.req 3 0 (.settle "p" .resolved "x"))),
   ("c", .app (.req 4 0 (.settle "p" .rejected "y"))),
   ("w", .app (.req 5 0 (.listen "p" "w"))), ("b", .app (.req 6 0 (.get "p")))]

def fuzzRuns (cfg : Config) : List (Experiment.Network.Execution system) :=
  (List.range 30).map fun seed => Experiment.Network.fuzz system cfg world inputs ["n1", "n2"] seed 16

#guard (fuzzRuns { flaky := true }).all (refines { flaky := true })

end Exp3

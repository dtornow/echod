import Experiment.Storage

/-!
# The promise service on object storage, run

Two nodes and a store. A scripted race, with and without conditional
writes, and fuzzed runs, each checked against the abstract service.
-/

namespace Experiment.Storage

open Experiment (Time Addr Request Msg Response Record Out failed hit)

def world : List (Addr × Local) := [("n1", .node {}), ("n2", .node {}), ("s3", .store {})]

/-- A scripted step: a client sends to a node, or the first message from
    one address to another is delivered (with outcome `j`). -/
inductive Script where
  | send (a to : Addr) (m : Msg)
  | move (from_ to : Addr) (j : Nat := 0)

def drive (cfg : Config) (script : List (Time × Script)) : Option (Network.Execution system) :=
  let rec go (c : Network.Conf system) : List (Time × Script) → Option (Network.Execution system)
    | [] => some []
    | (t, s) :: rest => do
      let act ← match s with
        | .send a to m => some (Network.Act.request a to (.app m))
        | .move f to j =>
          (c.net.findIdx? fun (w, w', _) => w.addr == f && w'.addr == to).map
            (fun i => Network.Act.deliver i j)
      let (l, o, c') ← c.take cfg t act
      let x ← go c' rest
      return (l, o, c') :: x
  go (Network.initial world) script

/-- A client's request, all the way through one node: in, load, decide,
    write, answer. -/
def through (a n : Addr) (id : Nat) (r : Request) (t : Time) : List (Time × Script) :=
  [(t, .send a n (.req id r)), (t, .move a n), (t, .move n "s3"), (t, .move "s3" n),
   (t, .move n "s3"), (t, .move "s3" n), (t, .move n a)]

/-! ## A race: two settles on two nodes

`a` settles `p` to `x` through `n1` while `b` settles it to `y` through
`n2`. Both load version 1; `n1` writes first. With conditional writes,
`n2`'s write is refused; it loads again, finds `p` settled, and answers
`b` with `x`, which is what the abstract service says the second settle
sees. Without, `n2` overwrites: both clients are told their own value. -/

def race : List (Time × Script) :=
  through "c" "n1" 1 (.create "p" (some 100)) 0 ++
  [(1, .send "a" "n1" (.req 2 (.settle "p" .resolved "x"))),
   (1, .send "b" "n2" (.req 3 (.settle "p" .rejected "y"))),
   (1, .move "a" "n1"), (1, .move "b" "n2"),       -- both ask for the document
   (1, .move "n1" "s3"), (1, .move "n2" "s3"),
   (1, .move "s3" "n1"), (1, .move "s3" "n2"),     -- both get version 1
   (1, .move "n1" "s3"), (1, .move "s3" "n1"),     -- n1 writes version 2
   (1, .move "n2" "s3"), (1, .move "s3" "n2")]     -- n2 writes on version 1

def settled (v : String) (st : Experiment.PromiseState) : Response :=
  ⟨200, some ⟨"p", st, v, 100⟩⟩

def answerTo (a : Addr) (x : Network.Execution system) : List Msg :=
  x.filterMap fun ((w, _, ev), _, _) =>
    match w, ev with
    | .client b, .receive _ (.app m) => if a == b then some m else none
    | _, _ => none

-- Conditional: n2 is refused, loads again, and answers b with a's value.
def safe := (drive {} (race ++ [(1, .move "n2" "s3"), (1, .move "s3" "n2"),
  (2, .move "n1" "a"), (2, .move "n2" "b")])).getD []

#guard safe.length == 23
#guard answerTo "a" safe == [.res 2 (settled "x" .resolved)]
#guard answerTo "b" safe == [.res 3 (settled "x" .resolved)]
#guard refines {} safe

-- Unconditional: n2 overwrites, and b is told its own value. No abstract
-- run shows that: the witness fails.
def lost := (drive { conditional := false } (race ++ [(2, .move "n1" "a"), (2, .move "n2" "b")])).getD []

#guard lost.length == 21
#guard answerTo "a" lost == [.res 2 (settled "x" .resolved)]
#guard answerTo "b" lost == [.res 3 (settled "y" .rejected)]
#guard !refines { conditional := false } lost

/-! ## A write that fails, having landed

The store takes `a`'s create but says it failed (outcome 1): `a` gets 503.
A later read sees the promise. The abstract service explains it: a 503
may have been done. -/

def ghost := (drive { flaky := true }
  ([(0, .send "a" "n1" (.req 1 (.create "p" (some 100)))), (0, .move "a" "n1"), (0, .move "n1" "s3"),
    (0, .move "s3" "n1"), (0, .move "n1" "s3" 1), (0, .move "s3" "n1"), (0, .move "n1" "a")] ++
   [(1, .send "b" "n2" (.req 2 (.get "p"))), (1, .move "b" "n2"), (1, .move "n2" "s3"),
    (1, .move "s3" "n2"), (1, .move "n2" "b")])).getD []

#guard answerTo "a" ghost == [.res 1 ⟨503, none⟩]
#guard answerTo "b" ghost == [.res 2 ⟨200, some ⟨"p", .pending, "", 100⟩⟩]
#guard refines { flaky := true } ghost

/-! ## Fuzzing

Three hundred runs of forty steps over two nodes and a flaky store:
creates, reads, settles both ways, a listener, and a timeout at 10 the
runs pass through. Every run refines the abstract service. -/

def inputs : List (Addr × CMsg) :=
  [("a", .app (.req 1 (.create "p" (some 10)))), ("a", .app (.req 2 (.get "p"))),
   ("b", .app (.req 3 (.settle "p" .resolved "x"))), ("c", .app (.req 4 (.settle "p" .rejected "y"))),
   ("w", .app (.req 5 (.listen "p" "w"))), ("b", .app (.req 6 (.get "p")))]

def fuzzRuns (cfg : Config) : List (Network.Execution system) :=
  (List.range 300).map fun seed => Network.fuzz system cfg world inputs ["n1", "n2"] seed 40

def count (p : CMsg → Bool) (runs : List (Network.Execution system)) : Nat :=
  (runs.map fun x => (x.filter fun ((_, _, ev), _, _) =>
    match ev with | .receive _ m => p m | _ => false).length).sum

end Experiment.Storage

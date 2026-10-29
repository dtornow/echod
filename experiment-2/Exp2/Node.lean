import Exp2.Proc
import Experiment.Storage
import Experiment.Check

/-!
# The storage node, written as a process

Experiment 1's node on object storage is a state machine: a table of
flights in progress, each in a phase, advanced by whichever answer of the
store arrives (`Storage.lean`, `nodeReceive`). Here the same node is code:
take a request, ask the store, wait for its answer, decide, write, wait,
answer. The phases are where the code waits; the flight table is the
continuation, and the mailbox holds what arrives in the meantime.

The node serves one request at a time: while it waits for the store, other
requests stay in its mailbox (selective receive). Two nodes still race
each other, through the store.

The store, the messages, the configuration and the abstract handlers are
experiment 1's, unchanged.
-/

namespace Exp2

open Experiment (Time Addr Some Out Service H Request Response Msg CallId pick sends)
open Experiment.Storage (CMsg Config Store storeReceive)
open Proc (send recv)

abbrev NodeP := Proc Config Nat CMsg

def fresh : NodeP Nat := do
  let n ← get
  set (n + 1)
  return n

def isRequest : Addr → CMsg → Bool
  | _, .app (.req _ _ _) => true
  | _, _ => false

def answers (op : Nat) : Addr → CMsg → Bool
  | _, .got o _ | _, .written o | _, .conflict o | _, .failed o => o == op
  | _, _ => false

def answer (c : Addr) (id : CallId) (res : Response) : NodeP Unit := send c (.app (.res id res))

def note : List (Out Msg) → NodeP Unit
  | [] => pure ()
  | .always n ok :: rest => do Proc.emit (.always n ok) (Proc.pure ()); note rest
  | .sometimes n hit :: rest => do Proc.emit (.sometimes n hit) (Proc.pure ()); note rest
  | .send _ _ :: rest => note rest

def sendAll : List (Addr × Msg) → NodeP Unit
  | [] => pure ()
  | (a, m) :: rest => do send a (.app m); sendAll rest

structure Candidate where
  client : Addr
  id     : CallId
  req    : Request
  now    : Time
  tries  : Nat
  doc    : Option (Experiment.Promise × Experiment.Storage.Version)
  res    : Response
  after  : Experiment.State
  outs   : List (Out Msg)
  promise : Experiment.Promise

/-- The residual process while a conditional write is outstanding. `retry`
is the structurally smaller recursive call supplied by `serve`. -/
def writeK (tries : Nat) (retry : (k : Nat) → k < tries → NodeP Unit)
    (cand : Candidate) (op : Nat) : NodeP Unit := do
  let (_, written, _) ← recv (answers op)
  match written with
  | .written _ => do answer cand.client cand.id cand.res; sendAll (sends cand.outs)
  | .conflict _ =>
    match tries with
    | k + 1 => retry k (Nat.lt_succ_self k)
    | 0 => answer cand.client cand.id ⟨503, none⟩
  | _ => answer cand.client cand.id ⟨503, none⟩

/-- Continue after the store returned the document. -/
def decideK (tries : Nat) (retry : (k : Nat) → k < tries → NodeP Unit)
    (c : Addr) (id : CallId) (r : Request) (now : Time)
    (cfg : Config) (doc : Option (Experiment.Promise × Experiment.Storage.Version))
    (before : Experiment.State) :
    Response × Experiment.State × List (Out Msg) → NodeP Unit
  | (res, after, outs) => do
    note outs
    if after == before then do
      answer c id res
      sendAll (sends outs)
    else
      match after.promises.find? (·.id == r.key) with
      | none => answer c id ⟨503, none⟩
      | some p =>
        let op ← fresh
        send cfg.store (.put op r.key p (doc.map (·.2)))
        writeK tries retry ⟨c, id, r, now, tries, doc, res, after, outs, p⟩ op

/-- The residual process while the document load is outstanding. -/
def loadK (tries : Nat) (retry : (k : Nat) → k < tries → NodeP Unit)
    (c : Addr) (id : CallId) (r : Request) (now : Time) (op : Nat) : NodeP Unit := do
  let (_, reply, _) ← recv (answers op)
  let .got _ doc := reply | answer c id ⟨503, none⟩
  let cfg ← read
  let before : Experiment.State := { promises := doc.toList.map (·.1) }
  decideK tries retry c id r now cfg doc before
    (pick ((Experiment.request r now).run cfg.app before) 0)

/-- One request, through: load, decide with the abstract handler, write
    conditionally, answer. `tries` more after a lost race. -/
def serve (c : Addr) (id : CallId) (r : Request) (now : Time) (tries : Nat) : NodeP Unit := do
  let cfg ← read
  let op ← fresh
  send cfg.store (.get op r.key)
  loadK tries (fun k _ => serve c id r now k) c id r now op
termination_by tries
decreasing_by omega

/-- The node: take the oldest request, serve it; over again. -/
def node : NodeP Unit := do
  let (c, m, _) ← recv isRequest
  match m with
  | .app (.req id now r) => serve c id r now (← read).retries
  | _ => return

/-! ## The system -/

inductive Local where
  | node (r : Running Config Nat CMsg)
  | store (s : Store)

def receive (sender : Addr) (m : CMsg) (now : Time) : H Config Local (Out CMsg) Unit :=
  fun e s =>
    match s with
    | .node r => ((toStep node 1000 sender m now) e r).map fun (a, r', w) => (a, .node r', w)
    | .store st => ((storeReceive sender m) e st).map fun (a, st', w) => (a, .store st', w)

abbrev system : Service where
  Config  := Config
  State   := Local
  Msg     := CMsg
  receive := receive
  tick    := fun _ => pure ()

def world : List (Addr × Local) :=
  [("n1", .node ⟨0, [], node⟩), ("n2", .node ⟨0, [], node⟩), ("s3", .store {})]

/-- What the clients saw, as the abstract world's trace. -/
def clientTrace (x : Experiment.Network.Execution system) : List (Experiment.Label Msg) :=
  x.filterMap fun ((who, t, ev), _, _) =>
    match who, ev with
    | .client a, .request _ (.app m) => some (.client a, t, .request m)
    | .client a, .receive _ (.app m) => some (.client a, t, .receive .server m)
    | _, _ => none

def refines (cfg : Config) (x : Experiment.Network.Execution system) : Bool :=
  Experiment.check Experiment.promises { cfg.app with unreliable := true } {} (clientTrace x)

/-! ## Runs -/

inductive Script where
  | send (a to : Addr) (m : Msg)
  | move (from_ to : Addr) (j : Nat := 0)

def Script.act? (c : Experiment.Network.Conf system) :
    Script → Option (Experiment.Network.Act system.Msg)
  | .send a to m => some (Experiment.Network.Act.request a to (.app m))
  | .move f to j =>
    (c.net.findIdx? fun (w, w', _) => w.addr == f && w'.addr == to).map
      (fun i => Experiment.Network.Act.deliver i j)

def driveFrom (cfg : Config) (c : Experiment.Network.Conf system) :
    List (Time × Script) → Option (Experiment.Network.Execution system)
  | [] => some []
  | (t, s) :: rest => do
    let act ← s.act? c
    let (l, o, c') ← c.take cfg t act
    let x ← driveFrom cfg c' rest
    return (l, o, c') :: x

def drive (cfg : Config) (script : List (Time × Script)) : Option (Experiment.Network.Execution system) :=
  driveFrom cfg (Experiment.Network.initial world) script

/-- Every execution returned by `drive` follows the network shell's rule. -/
theorem driveFrom_legal {c : Experiment.Network.Conf system}
    {script : List (Time × Script)} {x : Experiment.Network.Execution system}
    (h : driveFrom cfg c script = some x) :
    Experiment.Network.Legal system cfg c x := by
  induction script generalizing c x with
  | nil =>
    simp [driveFrom] at h
    subst h
    trivial
  | cons ts rest ih =>
    obtain ⟨t, s⟩ := ts
    simp only [driveFrom] at h
    obtain ⟨act, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨l, outs, c'⟩, ht, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨xs, hxs, h⟩ := Option.bind_eq_some_iff.mp h
    change some ((l, outs, c') :: xs) = some x at h
    simp only [Option.some.injEq] at h
    subst x
    exact ⟨⟨t, act, ht⟩, ih hxs⟩

theorem drive_legal {script : List (Time × Script)} {x : Experiment.Network.Execution system}
    (h : drive cfg script = some x) :
    Experiment.Network.Legal system cfg (Experiment.Network.initial world) x :=
  driveFrom_legal h

def answerTo (a : Addr) (x : Experiment.Network.Execution system) : List Msg :=
  x.filterMap fun ((w, _, ev), _, _) =>
    match w, ev with
    | .client b, .receive _ (.app m) => if a == b then some m else none
    | _, _ => none

def through (a n : Addr) (id : Nat) (r : Request) (t : Time) : List (Time × Script) :=
  [(t, .send a n (.req id t r)), (t, .move a n), (t, .move n "s3"), (t, .move "s3" n),
   (t, .move n "s3"), (t, .move "s3" n), (t, .move n a)]

def settled (v : String) (st : Experiment.PromiseState) : Response := ⟨200, some ⟨"p", st, v, 100⟩⟩

/-! ### Two settles racing on two nodes (experiment 1's race, same script) -/

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

/-! ### A request waits in the mailbox

`b`'s read reaches `n1` while `n1` waits for the store on `a`'s create.
It stays in the mailbox; `n1` serves it once the create is answered. -/

def queued := (drive {}
  [(0, .send "a" "n1" (.req 1 0 (.create "p" (some 100)))), (0, .move "a" "n1"),
   (0, .send "b" "n1" (.req 2 0 (.get "p"))), (0, .move "b" "n1"),      -- n1 is busy: queued
   (0, .move "n1" "s3"), (0, .move "s3" "n1"), (0, .move "n1" "s3"), (0, .move "s3" "n1"),
   (0, .move "n1" "s3"), (0, .move "s3" "n1"),                         -- now b's read
   (0, .move "n1" "a"), (0, .move "n1" "b")]).getD []

#guard queued.length == 12
#guard answerTo "b" queued == [.res 2 ⟨200, some ⟨"p", .pending, "", 100⟩⟩]
#guard refines {} queued

/-! ### Request time survives a delayed CAS

`a`'s request carries time 0 and creates a promise with absolute timeout 5.
Its conditional write is delayed. At time 10, `b` still reads the document as
absent and receives 404. Then `a`'s write lands and returns the pending promise
computed from its request time.

The abstract execution orders `b` before `a` while retaining time 0 as part of
`a`'s request. The later CAS instant does not change the handler input.
-/

def delayedCasScript : List (Time × Script) :=
  [(0, .send "a" "n1" (.req 1 0 (.create "p" (some 5)))),
   (0, .move "a" "n1"), (0, .move "n1" "s3"), (0, .move "s3" "n1"),
   (10, .send "b" "n2" (.req 2 10 (.get "p"))),
   (10, .move "b" "n2"), (10, .move "n2" "s3"), (10, .move "s3" "n2"),
   (10, .move "n2" "b"),
   (10, .move "n1" "s3"), (10, .move "s3" "n1"), (10, .move "n1" "a")]

def delayedCas := (drive {} delayedCasScript).getD []

theorem delayedCas_runs : drive {} delayedCasScript = some delayedCas := by
  have hs : (drive {} delayedCasScript).isSome = true := by native_decide
  cases h : drive {} delayedCasScript with
  | none => simp [h] at hs
  | some x =>
    have hx : delayedCas = x := by simp [delayedCas, h]
    rw [hx]

#guard delayedCas.length == 12
#guard answerTo "b" delayedCas == [.res 2 ⟨404, none⟩]
#guard answerTo "a" delayedCas ==
  [.res 1 ⟨200, some ⟨"p", .pending, "", 5⟩⟩]
#guard refines {} delayedCas

/-! ### Fuzzing, a little -/

def inputs : List (Addr × CMsg) :=
  [("a", .app (.req 1 0 (.create "p" (some 10)))), ("a", .app (.req 2 0 (.get "p"))),
   ("b", .app (.req 3 0 (.settle "p" .resolved "x"))),
   ("c", .app (.req 4 0 (.settle "p" .rejected "y"))),
   ("w", .app (.req 5 0 (.listen "p" "w"))), ("b", .app (.req 6 0 (.get "p")))]

def fuzzRuns (cfg : Config) : List (Experiment.Network.Execution system) :=
  (List.range 30).map fun seed => Experiment.Network.fuzz system cfg world inputs ["n1", "n2"] seed 16

#guard (fuzzRuns { flaky := true }).all (refines { flaky := true })

end Exp2

import Exp3.Caller
import Experiment.Storage
import Experiment.Check

/-!
# The storage node, as a caller

Experiment 1's node on object storage, a third time. A request waits at
one of two points: while its document loads, and while its write lands.
`Wait` names them, with what each needs. The rest is the protocol:

* a request: load its document;
* loaded: decide with the abstract handler; nothing changed, answer;
  something did, write it conditionally;
* written: answer, and send the step's notifications;
* refused: load again, if tries remain;
* anything else: 503.

Ids, the table of waiting calls and matching replies are the template's.
Requests do not wait for each other: a node has as many in flight as it
is sent. The store, the messages and the abstract handlers are experiment
1's, unchanged.
-/

namespace Exp3

open Experiment (Time Addr Some Out Service H Request Response Msg CallId pick sends)
open Experiment.Storage (CMsg Config Store storeReceive)

/-- Where a request waits. -/
inductive Wait where
  | loading (c : Addr) (id : CallId) (r : Request) (now : Time) (tries : Nat)
  | writing (c : Addr) (id : CallId) (r : Request) (now : Time)
      (res : Response) (notify : List (Addr × Msg)) (tries : Nat)

def Wait.client : Wait → Addr
  | .loading c .. | .writing c .. => c

def Wait.id : Wait → CallId
  | .loading _ id .. | .writing _ id .. => id

abbrev N := C Config Unit Wait CMsg

def answer (c : Addr) (id : CallId) (res : Response) : N Unit := C.send c (.app (.res id res))

def sendAll : List (Addr × Msg) → N Unit
  | [] => pure ()
  | (a, m) :: rest => do C.send a (.app m); sendAll rest

/-- The abstract handler's assertions, passed on. -/
def note : List (Out Msg) → N Unit
  | [] => pure ()
  | .always n ok :: rest => do C.emit (.always n ok); note rest
  | .sometimes n hit :: rest => do C.emit (.sometimes n hit); note rest
  | .send _ _ :: rest => note rest

def load (c : Addr) (id : CallId) (r : Request) (now : Time) (tries : Nat) : N Unit := do
  C.call (← read).store (fun op => .get op r.key) (.loading c id r now tries)

def replyTo : CMsg → Option Nat
  | .got op _ | .written op | .conflict op | .failed op => some op
  | _ => none

def receive (sender : Addr) (m : CMsg) (_ : Time) : N Unit :=
  match m with
  | .app (.req id now r) => do load sender id r now (← read).retries
  | _ => pure ()

/-- The abstract handler has run on the loaded document: answer, or write. -/
def decided (c : Addr) (id : CallId) (r : Request) (now : Time) (tries : Nat) (cfg : Config)
    (doc : Option (Experiment.Promise × Experiment.Storage.Version)) (before : Experiment.State) :
    Response × Experiment.State × List (Out Msg) → N Unit
  | (res, after, outs) => do
    note outs
    if after == before then do
      answer c id res
      sendAll (sends outs)
    else
      match after.promises.find? (·.id == r.key) with
      | none => answer c id ⟨503, none⟩
      | some p =>
        C.call cfg.store (fun op => .put op r.key p (doc.map (·.2)))
          (.writing c id r now res (sends outs) tries)

def resume (w : Wait) (_ : Addr) (m : CMsg) (_stepNow : Time) : N Unit :=
  match w, m with
  | .loading c id r now tries, .got _ doc => do
    let cfg ← read
    let before : Experiment.State := { promises := doc.toList.map (·.1) }
    decided c id r now tries cfg doc before
      (pick ((Experiment.dispatch r now).run { cfg.app with unreliable := true } before) 0)
  | .writing c id _ _ res notify _, .written _ => do
    answer c id res
    sendAll notify
  | .writing c id r now _ _ (k + 1), .conflict _ => load c id r now k
  | w, _ => answer w.client w.id ⟨503, none⟩

def node : Caller where
  Config  := Config
  State   := Unit
  Msg     := CMsg
  Wait    := Wait
  replyTo := replyTo
  receive := receive
  resume  := resume

/-! ## The node keeps the template's bookkeeping, so the template's
theorems hold of it -/

theorem sendAll_keeps (xs : List (Addr × Msg)) : Keeps (sendAll xs) := by
  induction xs with
  | nil => exact Keeps.pure _
  | cons x rest ih => exact Keeps.bind (Keeps.send _ _) fun _ => ih

theorem note_keeps (xs : List (Out Msg)) : Keeps (note xs) := by
  induction xs with
  | nil => exact Keeps.pure _
  | cons o rest ih =>
    cases o with
    | send _ _ => exact ih
    | always _ _ => exact Keeps.bind (Keeps.emit _) fun _ => ih
    | sometimes _ _ => exact Keeps.bind (Keeps.emit _) fun _ => ih

theorem load_keeps (c : Addr) (id : CallId) (r : Request) (now : Time) (k : Nat) :
    Keeps (load c id r now k) :=
  Keeps.bind Keeps.read fun _ => Keeps.call _ _ _

theorem decided_keeps (c : Addr) (id : CallId) (r : Request) (now : Time)
    (tries : Nat) (cfg : Config)
    (doc : Option (Experiment.Promise × Experiment.Storage.Version)) (before : Experiment.State) :
    ∀ x, Keeps (decided c id r now tries cfg doc before x) := by
  rintro ⟨res, after, outs⟩
  unfold decided
  refine Keeps.bind (note_keeps _) fun _ => ?_
  split
  · exact Keeps.bind (Keeps.send _ _) fun _ => sendAll_keeps _
  · split
    · exact Keeps.send _ _
    · exact Keeps.call _ _ _

theorem node_keeps : node.Keeps := by
  constructor
  · intro sender m now
    show Keeps (receive sender m now)
    unfold receive
    split
    · exact Keeps.bind Keeps.read fun _ => load_keeps _ _ _ _ _
    · exact Keeps.pure _
  · intro w sender m now
    show Keeps (resume w sender m now)
    unfold resume
    split
    · exact Keeps.bind Keeps.read fun _ => decided_keeps _ _ _ _ _ _ _ _ _
    · exact Keeps.bind (Keeps.send _ _) fun _ => sendAll_keeps _
    · exact load_keeps _ _ _ _ _
    · exact Keeps.send _ _

/-- No call of a node is resumed twice. -/
theorem node_once {s : Calls Unit Wait} (hs : Fresh s) {m : CMsg} {id : Nat} {w : Wait}
    (h : waitingFor node.replyTo s m = some (id, w)) (sender : Addr) (now : Time) (e : Config) :
    ∀ r ∈ (node.step sender m now e s).val, ∀ w', (id, w') ∉ r.2.1.waiting :=
  once node_keeps hs h sender now e

/-! ## The system -/

inductive Local where
  | node (s : Calls Unit Wait)
  | store (s : Store)

def step (sender : Addr) (m : CMsg) (now : Time) : H Config Local (Out CMsg) Unit :=
  fun e s =>
    match s with
    | .node st => (node.step sender m now e st).map fun (a, st', w) => (a, .node st', w)
    | .store st => ((storeReceive sender m) e st).map fun (a, st', w) => (a, .store st', w)

abbrev system : Service where
  Config  := Config
  State   := Local
  Msg     := CMsg
  receive := step
  tick    := fun _ => pure ()

def world : List (Addr × Local) := [("n1", .node { data := () }), ("n2", .node { data := () }), ("s3", .store {})]

/-- What the clients saw, as the abstract world's trace. -/
def clientTrace (x : Experiment.Network.Execution system) : List (Experiment.Label Msg) :=
  x.filterMap fun ((who, t, ev), _, _) =>
    match who, ev with
    | .client a, .request _ (.app m) => some (.client a, t, .request m)
    | .client a, .receive _ (.app m) => some (.client a, t, .receive .server m)
    | _, _ => none

def refines (cfg : Config) (x : Experiment.Network.Execution system) : Bool :=
  Experiment.check Experiment.promises { cfg.app with unreliable := true } {} (clientTrace x)

end Exp3

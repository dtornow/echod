import Kleppmann.Network
import «02-abstract».«system»

/-!
# Resonate, as a Kleppmann world

Two kinds of process: the Resonate server, and clients, each at an address.
Workers are clients too: the server dispatches `execute` and `unblock` to an
address, and whoever is at that address receives it.

* **The server's step function is the specification's**: a request arrives
  as a message, `Abstraction.handleExternal` answers it, and the answer goes
  back to the sender; a timeout names an internal step, and
  `Abstraction.handleInternal` runs it. The `setMessage` effects a step
  emits are the server's sends to workers. Nothing is re-implemented.
* **A client** turns user input into a request to the server, and keeps
  everything it receives.

Messages carry a client-chosen id, so a client can tell which response is
which; the spec's handlers never see it.
-/

namespace Kleppmann.Resonate

open ServerModel (Ident Message PromiseState)
open Equivalence (Request Response)
open Abstraction (InternalStep)

/-- The processes. -/
inductive Proc where
  | server
  | client (address : String)
  deriving DecidableEq, Repr

/-- What travels between them. -/
inductive Msg where
  /-- A client asks the server. -/
  | req (id : Nat) (rq : Request)
  /-- The server answers request `id`. -/
  | res (id : Nat) (r : Response)
  /-- The server tells a worker something on its own: `execute`, `unblock`. -/
  | msg (m : Message)
  deriving Repr

/-- User input at a client: send this request, under this id. -/
structure Input where
  id : Nat
  rq : Request
  deriving Repr

/-- A process's local state: the server's is the specification's; a
    client's is everything it has received. -/
inductive State where
  | server (s : AbstractModel.ServerState)
  | client (got : List Msg)
  deriving Repr

def init : Proc → State
  | .server => .server AbstractModel.ServerState.init
  | .client _ => .client []

/-- Run one of the specification's handlers: its result, the state it
    commits, and its dispatches, as sends to the addressed clients. -/
def serve {α : Type} (mat : Bool) (s : AbstractModel.ServerState) (act : AbstractModel.H α) :
    α × AbstractModel.ServerState × List (Proc × Msg) :=
  let (a, effs) := act { state := s, mat := mat }
  (a, AbstractModel.applyAll s effs,
   effs.filterMap fun | .setMessage addr m => some (.client addr, .msg m) | _ => none)

/-- The step function. `mat`: the specification's read discipline. -/
def step (mat : Bool) : StepFunc Proc State Msg Input InternalStep
  | .server, .server s, now, .receive (.client c) (.req id rq) =>
      let (r, s', out) := serve mat s (Abstraction.handleExternal rq now)
      (.server s', (.client c, .res id r) :: out)
  | .server, .server s, now, .timeout which =>
      let (_, s', out) := serve mat s (Abstraction.handleInternal which now)
      (.server s', out)
  | .client _, .client got, _, .request i => (.client got, [(.server, .req i.id i.rq)])
  | .client _, .client got, _, .receive .server m => (.client (got ++ [m]), [])
  | _, st, _, _ => (st, [])

/-- Every process exists: any address may be a client. -/
def procs : Proc → Prop := fun _ => True

abbrev Exec (mat : Bool) := Execute (step mat) init procs

/-! ## Running it

An execution is chosen one step at a time: user input at a client, a
timeout at the server, or the delivery of the `k`-th message ever sent.
Delivering by position is what makes every receive valid: the message is
in the network because that is where it was taken from. -/

/-- One choice of the world. -/
inductive Act where
  | input (address : String) (i : Input)
  | timeout (which : InternalStep)
  | deliver (k : Nat)

/-- A run so far: the events, the network, the states, the clock. -/
structure Run where
  events : List (Proc × Time × Event Proc Msg Input InternalStep) := []
  msgs   : List (Proc × Proc × Msg) := []
  states : Proc → State := init
  clock  : Time := 0

/-- Take one step at `now`; `none` if the choice is impossible (the clock
    would go back, or there is no `k`-th message). -/
def Run.take (mat : Bool) (r : Run) (now : Time) : Act → Option Run
  | a =>
    if now < r.clock then none else
    let ev? : Option (Proc × Event Proc Msg Input InternalStep) := match a with
      | .input c i => some (.client c, .request i)
      | .timeout w => some (.server, .timeout w)
      | .deliver k => (r.msgs[k]?).map fun (from_, to, m) => (to, .receive from_ m)
    ev?.map fun (proc, ev) =>
      let (new, sent) := step mat proc (r.states proc) now ev
      { events := r.events ++ [(proc, now, ev)]
        msgs   := r.msgs ++ sent.map fun (recpt, msg) => (proc, recpt, msg)
        states := fun p => if p = proc then new else r.states p
        clock  := now }

def simulate (mat : Bool) (acts : List (Time × Act)) : Option Run :=
  acts.foldlM (fun r (now, a) => r.take mat now a) {}

/-- What a client has received. -/
def Run.got (r : Run) (c : String) : List Msg :=
  match r.states (.client c) with
  | .client got => got
  | .server _ => []

/-! ## A scenario

A client creates a promise that times out at 10, and reads it back at 5 and
at 20. The second read sees it timed out: the spec projects the promise at
the instant of the read. -/

def p : Ident := { origin := "o", suffix := "p" }

def create : Request := .promiseCreate { id := p, timeoutAt := 10, param := {}, tags := [] }
def get : Request := .promiseGet { id := p }

def scenario : List (Time × Act) :=
  [ (0, .input "c" ⟨1, create⟩), (0, .deliver 0), (0, .deliver 1),
    (5, .input "c" ⟨2, get⟩),    (5, .deliver 2), (5, .deliver 3),
    (20, .input "c" ⟨3, get⟩),   (20, .deliver 4), (20, .deliver 5) ]

def stateOf : Response → Option PromiseState
  | .promiseCreate r => r.promise.map (·.state)
  | .promiseGet r => r.promise.map (·.state)
  | _ => none

/-- What the client saw: for each response, the promise state it reports. -/
def seen (r : Run) : List (Nat × Option PromiseState) :=
  (r.got "c").filterMap fun | .res id res => some (id, stateOf res) | _ => none

#guard ((simulate true scenario).map seen) ==
  some [(1, some .pending), (2, some .pending), (3, some .rejectedTimedout)]

-- The network keeps everything: delivering the first response again is valid,
-- and the client now holds it twice.
#guard (((simulate true (scenario ++ [(20, .deliver 1)])).map fun r => (r.got "c").length)) == some 4

-- Time does not go back.
#guard (simulate true (scenario ++ [(19, .input "c" ⟨4, get⟩)])).isNone

/-! ## A property, proved his way

A client only ever holds a response to a request it sent. Kleppmann's
method: state it of the network, show the empty network has it, show every
step keeps it. -/

/-- Every response the server sent answers a request that client sent. -/
def Answered (msgs : List (Proc × Proc × Msg)) : Prop :=
  ∀ c id r, (Proc.server, Proc.client c, Msg.res id r) ∈ msgs →
    ∃ rq, (Proc.client c, Proc.server, Msg.req id rq) ∈ msgs

/-- The dispatches of a handler are `msg`s, never responses. -/
theorem serve_no_res {α : Type} {mat : Bool} {s : AbstractModel.ServerState}
    {act : AbstractModel.H α} {c : String} {id : Nat} {r : Response} :
    (Proc.client c, Msg.res id r) ∉ (serve mat s act).2.2 := by
  intro h
  simp only [serve, List.mem_filterMap] at h
  obtain ⟨e, _, he⟩ := h
  cases e <;> simp at he

/-- A step sends a response only to a client whose request it just received. -/
theorem step_res {mat : Bool} {proc : Proc} {st : State} {now : Time}
    {ev : Event Proc Msg Input InternalStep} {new : State} {sent : List (Proc × Msg)}
    {c : String} {id : Nat} {r : Response}
    (h : step mat proc st now ev = (new, sent)) (hm : (Proc.client c, Msg.res id r) ∈ sent) :
    proc = .server ∧ ∃ rq, ev = .receive (.client c) (.req id rq) := by
  unfold step at h
  split at h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨-, rfl⟩ := h
  · rename_i c' id' rq'
    simp only [List.mem_cons, Prod.mk.injEq, Proc.client.injEq] at hm
    rcases hm with ⟨rfl, h2⟩ | hm
    · cases h2; exact ⟨rfl, rq', rfl⟩
    · exact absurd hm serve_no_res
  · exact absurd hm serve_no_res
  · simp at hm
  · simp at hm
  · simp at hm

/-- In every execution, every response a client can receive answers a
    request it sent. -/
theorem answered {mat : Bool} {events msgs states clock}
    (h : Exec mat events msgs states clock) : Answered msgs := by
  refine Execute.invariant (inv := fun msgs _ => Answered msgs) ?_ ?_ h
  · intro c id r hm; simp at hm
  · intro msgs states clock proc now event new sent ih _ _ hv hs c id r hm
    simp only [List.mem_append, List.mem_map, Prod.mk.injEq] at hm
    rcases hm with hm | ⟨⟨recpt, msg⟩, hsent, rfl, rfl, rfl⟩
    · obtain ⟨rq, hrq⟩ := ih c id r hm
      exact ⟨rq, List.mem_append_left _ hrq⟩
    · obtain ⟨-, rq, rfl⟩ := step_res hs hsent
      exact ⟨rq, List.mem_append_left _ hv⟩

end Kleppmann.Resonate

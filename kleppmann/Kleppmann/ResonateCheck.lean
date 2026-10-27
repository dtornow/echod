import Kleppmann.Check
import «02-abstract».«system»

/-!
# Checking Resonate traces

Resonate as a model of the world in `World.lean`, built from the
specification's own handlers:

* `external` is `Abstraction.handleExternal`; its `setMessage` effects are
  what the system sends workers on the side.
* `tick` is a sweep: `Abstraction.handleInternal` run on every candidate
  in turn, and the sweep repeated while it changes something (a lease that
  runs out makes a retry possible). The candidates come from the state: an
  object's promise timeout, the callbacks and listeners of a settled
  promise, a task's lease and retry, an armed schedule. No queue: the state
  already says what is pending, and each handler decides whether it is due.
  One outcome: the server does everything that is due when it is ticked.

Promise timeouts need no tick to be seen: a read projects a promise at the
instant of the read. A lease does: until the server is ticked, the task is
still held.
-/

namespace Kleppmann.ResonateCheck

open Kleppmann.World
open ServerModel (Ident Message PromiseState TaskState)
open Equivalence (Request Response)
open Abstraction (InternalStep)

open ServerModel in
deriving instance DecidableEq for Value, PromiseRecord, TaskRecord, Schedule,
  PromiseGetRes, PromiseCreateRes, PromiseSettleRes, PromiseRegisterCallbackRes,
  PromiseRegisterListenerRes, PromiseSearchRes, ScheduleGetRes, ScheduleCreateRes,
  ScheduleDeleteRes, ScheduleSearchRes, TaskGetRes, TaskCreateRes, TaskAcquireRes,
  TaskFenceInnerRes, TaskFenceRes, TaskHeartbeatRes, TaskSuspendRes, TaskFulfillRes,
  TaskReleaseRes, TaskHaltRes, TaskContinueRes, TaskSearchRes, Message
deriving instance DecidableEq for Equivalence.Response

abbrev ServerState := AbstractModel.ServerState

/-- Run one of the specification's handlers: its result, the state it
    commits, and its dispatches, by address. -/
def serve {α : Type} (s : ServerState) (act : AbstractModel.H α) :
    α × ServerState × List (Client × Message) :=
  let (a, effs) := act { state := s, mat := true }
  (a, AbstractModel.applyAll s effs,
   effs.filterMap fun | .setMessage addr msg => some (addr, msg) | _ => none)

/-- Internal steps that might apply: everything the state holds that an
    internal step looks at. Which of them do anything is up to the handler. -/
def candidates (s : ServerState) (now : Nat) : List InternalStep :=
  (s.objects.flatMap fun o =>
    let settled := (o.promise.project now).state != .pending
    [.promiseTimeout ⟨o.id⟩] ++
    (if settled then o.promise.callbacks.map (fun a => .callback ⟨o.id, a⟩) else []) ++
    (if settled then o.promise.listeners.map (fun a => .listener ⟨o.id, a⟩) else []) ++
    (match o.task with
     | some _ => [.taskLeaseTimeout ⟨o.id⟩, .taskRetryTimeout ⟨o.id⟩]
     | none => [])) ++
  s.schedules.map fun sc => .scheduleTimeout ⟨sc.id⟩

/-- One pass: every candidate, in turn, at `now`. -/
def pass (s : ServerState) (now : Nat) : ServerState × List (Client × Message) :=
  (candidates s now).foldl (fun (s, out) w =>
    let (_, s', out') := serve s (Abstraction.handleInternal w now)
    (s', out ++ out')) (s, [])

/-- Passes until nothing changes (at most `fuel`). -/
def sweep (s : ServerState) (now : Nat) : Nat → ServerState × List (Client × Message)
  | 0 => (s, [])
  | fuel + 1 =>
    let (s', out) := pass s now
    if s' == s && out.isEmpty then (s, [])
    else let (s'', out') := sweep s' now fuel; (s'', out ++ out')

abbrev resonate : Model where
  State    := ServerState
  Request  := Request
  Response := Response
  Dispatch := Message
  external := fun r s now =>
    let (resp, s', out) := serve s (Abstraction.handleExternal r now)
    .one ⟨s', resp, out⟩
  tick := fun s now =>
    let (s', out) := sweep s now 4
    .one ⟨s', out⟩

/-! ## Traces

The responses in these traces are computed by running the specification
directly, in the order the scenario intends, and then the checker is asked
whether the trace, as clients saw it, could have happened. -/

/-- The specification's answer to `r` at `now`, and the state after. -/
def answer (s : ServerState) (r : Request) (now : Nat) : Response × ServerState :=
  let (resp, s', _) := serve s (Abstraction.handleExternal r now)
  (resp, s')

/-- A client sends a request and receives its response. -/
def call (a : Client) (t : Time) (id : CallId) (r : Request) (res : Response) :
    List (Proc × Time × Event resonate) :=
  [(.client a, t, .request id r), (.client a, t, .receive .server (.res id res))]

def tick (t : Time) : List (Proc × Time × Event resonate) := [(.server, t, .timeout)]

def p : Ident := { origin := "o", suffix := "p" }

def create (timeoutAt : Nat) : Request :=
  .promiseCreate { id := p, timeoutAt := timeoutAt, param := {}, tags := [] }
def get : Request := .promiseGet { id := p }

/-! ### A promise read before and after its timeout -/

def s₀ : ServerState := AbstractModel.ServerState.init
def r₁ := answer s₀ (create 10) 0
def r₂ := answer r₁.2 get 5
def r₃ := answer r₂.2 get 20

def timeouts (third : Response) : List (Proc × Time × Event resonate) :=
  call "c" 0 1 (create 10) r₁.1 ++ call "c" 5 2 get r₂.1 ++ call "c" 20 3 get third

#guard check resonate s₀ 2 (timeouts r₃.1)
-- After the timeout a read cannot see the promise pending, ticked or not.
#guard !check resonate s₀ 2 (timeouts r₂.1)

/-! ### Two clients: the window is causality

`a` creates the promise while `b` reads it. If `b`'s read overlaps the
create, it may see nothing (404) or the promise; if `b` only asks after `a`
was answered, the create took effect before, and 404 is impossible. No rule
says so: `a`'s answer was sent when the system took the create, and `b`'s
request was sent after `a` received it. -/

def missing : Response := (answer s₀ get 0).1
def found : Response := (answer r₁.2 get 0).1

def overlapping (seen : Response) : List (Proc × Time × Event resonate) :=
  [(.client "a", 0, .request 1 (create 10)), (.client "b", 0, .request 2 get),
   (.client "b", 0, .receive .server (.res 2 seen)), (.client "a", 0, .receive .server (.res 1 r₁.1))]

#guard check resonate s₀ 2 (overlapping missing)
#guard check resonate s₀ 2 (overlapping found)
#guard check resonate s₀ 2 (call "a" 0 1 (create 10) r₁.1 ++ call "b" 0 2 get found)
#guard !check resonate s₀ 2 (call "a" 0 1 (create 10) r₁.1 ++ call "b" 0 2 get missing)

/-! ### A lease that runs out: the tick is in the trace

A task is created held by worker `w1` with a lease of 10, targeted at
address `w`. The driver ticks the server at 50: the lease has run out, so
the server releases the task and re-offers it, which sends `w` an
`execute`. A read at 50 sees the task pending again. Without the tick the
server has done nothing, and the task is still held. -/

def taskP : Request :=
  .taskCreate { pid := "w1", ttl := 10,
                action := { id := p, timeoutAt := 1000, param := {}, tags := [("resonate:target", "w")] } }
def taskGet : Request := .taskGet { id := p }

def t₁ := answer s₀ taskP 0
/-- The state at 50 after the two steps that are due: the lease runs out,
    then the task is re-offered. Computed directly, not by the sweep. -/
def t₂ := (serve (serve t₁.2 (Abstraction.handleInternal (.taskLeaseTimeout ⟨p⟩) 50)).2.1
             (Abstraction.handleInternal (.taskRetryTimeout ⟨p⟩) 50))
def released := (answer t₂.2.1 taskGet 50).1
def stillHeld := (answer t₁.2 taskGet 50).1
def offer : Message := (t₂.2.2.head?.map (·.2)).getD (.execute p 0)

def lease (seen : Response) : List (Proc × Time × Event resonate) :=
  call "c" 0 1 taskP t₁.1 ++ tick 50 ++ call "c" 50 2 taskGet seen

#guard check resonate s₀ 2 (lease released)
-- Ticked at 50, past the lease: the task cannot still be held.
#guard !check resonate s₀ 2 (lease stillHeld)
-- And the worker at `w` receives the re-offer.
#guard check resonate s₀ 2 (lease released ++ [(.client "w", 50, .receive .server (.out offer))])
-- Not ticked: the task is still held, and there is no re-offer to receive.
#guard check resonate s₀ 2 (call "c" 0 1 taskP t₁.1 ++ call "c" 50 2 taskGet stillHeld)
#guard !check resonate s₀ 2 (call "c" 0 1 taskP t₁.1 ++ call "c" 50 2 taskGet released)
#guard !check resonate s₀ 2 (call "c" 0 1 taskP t₁.1 ++ [(.client "w", 50, .receive .server (.out offer))])
-- Ticked too early, at 5: nothing is due yet.
#guard check resonate s₀ 2 (call "c" 0 1 taskP t₁.1 ++ tick 5 ++ call "c" 50 2 taskGet stillHeld)

end Kleppmann.ResonateCheck

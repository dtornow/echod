import Kleppmann.Check
import «02-abstract».«system»

/-!
# Checking Resonate traces

Resonate as a model of the world in `World.lean`, built from the
specification's own handlers:

* `external` is `Abstraction.handleExternal`; its `setMessage` effects are
  what the system sends workers on the side.
* `tick` is every internal step that would change something now:
  `Abstraction.handleInternal` run on each candidate, and kept if it does.
  The candidates come from the state: an object's promise timeout, the
  callbacks and listeners of a settled promise, a held task's lease, a
  pending task's retry, an armed schedule. No queue: the state already says
  what is pending.
* `due` is when something must have happened by: a held task's lease, a
  pending task's retry, a schedule's next run, all read off the state. Promise
  timeouts are not in it: a read projects a promise at the instant of the
  read, so a timed-out promise is seen timed out whether or not a step ran.
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

/-- When something must have happened by: a held task's lease and a pending
    task's retry, while its promise is pending; a schedule's next run. -/
def dueOf (s : ServerState) : Option Nat :=
  let times := (s.objects.filterMap fun o =>
      match o.task with
      | some t =>
          if o.promise.state != .pending then none
          else if t.state == .acquired then t.leaseTimeoutAt
          else if t.state == .pending then t.retryTimeoutAt
          else none
      | none => none) ++
    s.schedules.map (·.nextRunAt)
  times.min?

abbrev resonate : Model where
  State    := ServerState
  Request  := Request
  Response := Response
  Dispatch := Message
  external := fun r s now =>
    let (resp, s', out) := serve s (Abstraction.handleExternal r now)
    .one ⟨s', resp, out⟩
  tick := fun s now =>
    (candidates s now).filterMap fun w =>
      let (_, s', out) := serve s (Abstraction.handleInternal w now)
      if s' == s && out.isEmpty then none else some ⟨s', out⟩
  due := dueOf

/-! ## Traces

The responses in these traces are computed by running the specification
directly, in the order the scenario intends, and then the checker is asked
whether the trace, as clients saw it, could have happened. -/

/-- The specification's answer to `r` at `now`, and the state after. -/
def answer (s : ServerState) (r : Request) (now : Nat) : Response × ServerState :=
  let (resp, s', _) := serve s (Abstraction.handleExternal r now)
  (resp, s')

/-- A client sends a request and receives its response. -/
def call (a : Client) (id : CallId) (r : Request) (res : Response) : List (Proc × Event resonate) :=
  [(.client a, .request id r), (.client a, .receive .sys (.res id res))]

def p : Ident := { origin := "o", suffix := "p" }

def create (timeoutAt : Nat) : Request :=
  .promiseCreate { id := p, timeoutAt := timeoutAt, param := {}, tags := [] }
def get : Request := .promiseGet { id := p }

/-! ### A promise read before and after its timeout -/

def s₀ : ServerState := AbstractModel.ServerState.init
def r₁ := answer s₀ (create 10) 0
def r₂ := answer r₁.2 get 5
def r₃ := answer r₂.2 get 20

def timeouts (third : Response) : List (Proc × Event resonate) :=
  call "c" 1 (create 10) r₁.1 ++ call "c" 2 get r₂.1 ++ [(.clock, .time 20)] ++ call "c" 3 get third

#guard check resonate s₀ 2 (timeouts r₃.1)
-- After the timeout a read cannot see the promise pending.
#guard !check resonate s₀ 2 (timeouts r₂.1)

/-! ### Two clients: the window is causality

`a` creates the promise while `b` reads it. If `b`'s read overlaps the
create, it may see nothing (404) or the promise; if `b` only asks after `a`
was answered, the create took effect before, and 404 is impossible. No rule
says so: `a`'s answer was sent when the system took the create, and `b`'s
request was sent after `a` received it. -/

def missing : Response := (answer s₀ get 0).1
def found : Response := (answer r₁.2 get 0).1

def overlapping (seen : Response) : List (Proc × Event resonate) :=
  [(.client "a", .request 1 (create 10)), (.client "b", .request 2 get),
   (.client "b", .receive .sys (.res 2 seen)), (.client "a", .receive .sys (.res 1 r₁.1))]

#guard check resonate s₀ 2 (overlapping missing)
#guard check resonate s₀ 2 (overlapping found)
#guard check resonate s₀ 2 (call "a" 1 (create 10) r₁.1 ++ call "b" 2 get found)
#guard !check resonate s₀ 2 (call "a" 1 (create 10) r₁.1 ++ call "b" 2 get missing)

/-! ### A lease that runs out: what is due goes first

A task is created held by worker `w1` with a lease of 10, targeted at
address `w`. At 50 the lease has run out, so before anything else is
observed the system must release the task and re-offer it, which sends
`w` an `execute`. A read at 50 sees the task pending again. -/

def taskP : Request :=
  .taskCreate { pid := "w1", ttl := 10,
                action := { id := p, timeoutAt := 1000, param := {}, tags := [("resonate:target", "w")] } }
def taskGet : Request := .taskGet { id := p }

def t₁ := answer s₀ taskP 0
/-- The state at 50 after the two steps that are due: the lease runs out,
    then the task is re-offered. -/
def t₂ := (serve (serve t₁.2 (Abstraction.handleInternal (.taskLeaseTimeout ⟨p⟩) 50)).2.1
             (Abstraction.handleInternal (.taskRetryTimeout ⟨p⟩) 50))
def released := (answer t₂.2.1 taskGet 50).1
def stillHeld := (answer t₁.2 taskGet 50).1
def offer : Message := (t₂.2.2.head?.map (·.2)).getD (.execute p 0)

def lease (seen : Response) : List (Proc × Event resonate) :=
  call "c" 1 taskP t₁.1 ++ [(.clock, .time 50)] ++ call "c" 2 taskGet seen

#guard check resonate s₀ 3 (lease released)
-- The lease was due at 10: by 50 the task cannot still be held.
#guard !check resonate s₀ 3 (lease stillHeld)
-- And the worker at `w` may receive the re-offer.
#guard check resonate s₀ 3 (lease released ++ [(.client "w", .receive .sys (.out offer))])
-- Before the lease runs out, no re-offer exists to receive.
#guard !check resonate s₀ 3 (call "c" 1 taskP t₁.1 ++ [(.client "w", .receive .sys (.out offer))])

end Kleppmann.ResonateCheck

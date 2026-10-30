import Rover.World
import Resonate.Internal

/-!
# Full Resonate protocol and direct abstract semantics

The request, response, record, schedule, task, and emitted-message payloads
below are the public types from the pinned `resonatehq/resonate`
specification. Rover adds only transport envelopes and request correlation.
-/

namespace Resonate

open Rover
open ServerModel

abbrev Addr := String
abbrev CallId := Nat
abbrev Request := Equivalence.Request
abbrev Response := Equivalence.Response
abbrev InternalStep := Abstraction.InternalStep

/-- Runtime handler settings plus the abstract availability policy used by
the concrete refinement. The direct handlers consume only `server`; the
Rover-level model uses `unreliable` to admit infrastructure failure paths. -/
structure Config extends Direct.ServerConfig where
  unreliable : Bool := false
  deriving Repr

deriving instance DecidableEq for PromiseGetReq
deriving instance DecidableEq for PromiseCreateReq
deriving instance DecidableEq for PromiseSettleReq
deriving instance DecidableEq for PromiseSearchReq
deriving instance DecidableEq for ScheduleGetReq
deriving instance DecidableEq for ScheduleCreateReq
deriving instance DecidableEq for ScheduleDeleteReq
deriving instance DecidableEq for ScheduleSearchReq
deriving instance DecidableEq for TaskGetReq
deriving instance DecidableEq for TaskCreateReq
deriving instance DecidableEq for TaskAcquireReq
deriving instance DecidableEq for TaskFenceAction
deriving instance DecidableEq for TaskFenceReq
deriving instance DecidableEq for TaskRef
deriving instance DecidableEq for TaskHeartbeatReq
deriving instance DecidableEq for TaskSuspendReq
deriving instance DecidableEq for TaskFulfillReq
deriving instance DecidableEq for TaskReleaseReq
deriving instance DecidableEq for TaskHaltReq
deriving instance DecidableEq for TaskContinueReq
deriving instance DecidableEq for TaskSearchReq
deriving instance DecidableEq for PromiseGetRes
deriving instance DecidableEq for PromiseCreateRes
deriving instance DecidableEq for PromiseSettleRes
deriving instance DecidableEq for PromiseRegisterCallbackRes
deriving instance DecidableEq for PromiseRegisterListenerRes
deriving instance DecidableEq for PromiseSearchRes
deriving instance DecidableEq for TaskFenceInnerRes
deriving instance DecidableEq for ScheduleGetRes
deriving instance DecidableEq for ScheduleCreateRes
deriving instance DecidableEq for ScheduleDeleteRes
deriving instance DecidableEq for ScheduleSearchRes
deriving instance DecidableEq for TaskGetRes
deriving instance DecidableEq for TaskCreateRes
deriving instance DecidableEq for TaskAcquireRes
deriving instance DecidableEq for TaskFenceRes
deriving instance DecidableEq for TaskHeartbeatRes
deriving instance DecidableEq for TaskSuspendRes
deriving instance DecidableEq for TaskFulfillRes
deriving instance DecidableEq for TaskReleaseRes
deriving instance DecidableEq for TaskHaltRes
deriving instance DecidableEq for TaskContinueRes
deriving instance DecidableEq for TaskSearchRes
deriving instance DecidableEq for Equivalence.Request
deriving instance DecidableEq for Equivalence.Response

deriving instance BEq for PromiseGetReq
deriving instance BEq for PromiseCreateReq
deriving instance BEq for PromiseSettleReq
deriving instance BEq for PromiseRegisterCallbackReq
deriving instance BEq for PromiseRegisterListenerReq
deriving instance BEq for PromiseSearchReq
deriving instance BEq for ScheduleGetReq
deriving instance BEq for ScheduleCreateReq
deriving instance BEq for ScheduleDeleteReq
deriving instance BEq for ScheduleSearchReq
deriving instance BEq for TaskGetReq
deriving instance BEq for TaskCreateReq
deriving instance BEq for TaskAcquireReq
deriving instance BEq for TaskFenceAction
deriving instance BEq for TaskFenceReq
deriving instance BEq for TaskRef
deriving instance BEq for TaskHeartbeatReq
deriving instance BEq for TaskSuspendReq
deriving instance BEq for TaskFulfillReq
deriving instance BEq for TaskReleaseReq
deriving instance BEq for TaskHaltReq
deriving instance BEq for TaskContinueReq
deriving instance BEq for TaskSearchReq
deriving instance BEq for Equivalence.Request

structure Call where
  client : Addr
  id : CallId
  requestedAt : Time
  request : Request
  deriving Repr, BEq, DecidableEq

/-- Publicly observable emissions: correlated replies and boundary messages. -/
inductive Output where
  | response (client : Addr) (id : CallId) (response : Response)
  | message (entry : OutboxEntry)
  deriving Repr, BEq, DecidableEq

def unavailableResponse : Request → Response
  | .promiseGet _ => .promiseGet { status := 503 }
  | .promiseCreate _ => .promiseCreate { status := 503, promise := none }
  | .promiseSettle _ => .promiseSettle { status := 503 }
  | .promiseRegisterCallback _ =>
      .promiseRegisterCallback { status := 503 }
  | .promiseRegisterListener _ =>
      .promiseRegisterListener { status := 503 }
  | .promiseSearch _ => .promiseSearch { status := 503 }
  | .scheduleGet _ => .scheduleGet { status := 503 }
  | .scheduleCreate _ => .scheduleCreate { status := 503 }
  | .scheduleDelete _ => .scheduleDelete { status := 503 }
  | .scheduleSearch _ => .scheduleSearch { status := 503 }
  | .taskGet _ => .taskGet { status := 503 }
  | .taskCreate _ => .taskCreate { status := 503 }
  | .taskAcquire _ => .taskAcquire { status := 503 }
  | .taskFence _ => .taskFence { status := 503 }
  | .taskHeartbeat _ => .taskHeartbeat { status := 503 }
  | .taskSuspend _ => .taskSuspend { status := 503 }
  | .taskFulfill _ => .taskFulfill { status := 503 }
  | .taskRelease _ => .taskRelease { status := 503 }
  | .taskHalt _ => .taskHalt { status := 503 }
  | .taskContinue _ => .taskContinue { status := 503 }
  | .taskSearch _ => .taskSearch { status := 503 }

def unavailable (call : Call) : Output :=
  .response call.client call.id (unavailableResponse call.request)

inductive Message where
  | request (call : Call)
  | output (output : Output)
  deriving Repr, DecidableEq

inductive BoundaryEvent where
  | request (time : Time) (call : Call)
  | response (time : Time) (client : Addr) (id : CallId)
      (response : Response)
  | message (time : Time) (entry : OutboxEntry)
  deriving Repr, BEq, DecidableEq

def Message.observeInput (time : Time) : Message → Option BoundaryEvent
  | .request call => some (.request time call)
  | _ => none

def Message.observeOutput (time : Time) : Message → Option BoundaryEvent
  | .output (.response client id response) =>
      some (.response time client id response)
  | .output (.message entry) => some (.message time entry)
  | _ => none

/-- Run one fixed-key handler against the process store. This is the only
global-store bridge used by external and internal dispatch. -/
def runDocument (config : Config) (key : DocumentKey)
    (handler : Direct.Handler key α) (state : State) :
    α × State × List OutboxEntry :=
  let (value, store, emitted) :=
    Direct.runWith config.toServerConfig key handler state.store
  (value, { state with store }, emitted)

theorem runDocument_frame (config : Config) (key other : DocumentKey)
    (handler : Direct.Handler key α) (state : State) (h : other ≠ key) :
    (runDocument config key handler state).2.1.store.read other =
      state.store.read other := by
  simp [runDocument, Direct.runWith, h]

theorem runDocument_atMostOne (config : Config) (key : DocumentKey)
    (handler : Direct.Handler key α) (state : State) :
    Direct.Store.AtMostOneDocument state.store
      (runDocument config key handler state).2.1.store := by
  right
  refine ⟨key, ?_⟩
  intro other h
  exact runDocument_frame config key other handler state h

def pureRequest (response : Response) (state : State) :
    Response × State × List OutboxEntry :=
  (response, state, [])

def sameOriginRefs (origin : String) (refs : List TaskRef) : Bool :=
  refs.all (·.id.origin == origin)

def WorkItem.key : WorkItem → DocumentKey
  | .promiseTimeout id => .origin id.origin
  | .callback req => .origin req.awaited.origin
  | .listener req => .origin req.awaited.origin
  | .taskLeaseTimeout id => .origin id.origin
  | .taskRetryTimeout id => .origin id.origin
  | .scheduleTimeout id => .schedule id
  | .occurrence req _ => .origin req.id.origin

def WorkflowEntry.key : WorkflowEntry → DocumentKey
  | .scan key _ => key
  | .work item _ => item.key

/-- Dispatch all 21 public operations. Multi-id requests are rejected before a
document is supplied unless every touched id has one origin. Unsupported
searches are process-level pure responses. -/
def handleExternal (config : Config) (request : Request) (now : Time)
    (state : State) : Response × State × List OutboxEntry :=
  match request with
  | .promiseGet req =>
      let (res, next, out) :=
        runDocument config (.origin req.id.origin)
          (Direct.promiseGet req now) state
      (.promiseGet res, next, out)
  | .promiseCreate req =>
      let (res, next, out) :=
        runDocument config (.origin req.id.origin)
          (Direct.promiseCreate req now) state
      (.promiseCreate res, next, out)
  | .promiseSettle req =>
      let (res, next, out) :=
        runDocument config (.origin req.id.origin)
          (Direct.promiseSettle req now) state
      (.promiseSettle res, next, out)
  | .promiseRegisterCallback req =>
      if !req.awaited.sameOrigin req.awaiter then
        pureRequest (.promiseRegisterCallback { status := 400 }) state
      else
        let (res, next, out) :=
          runDocument config (.origin req.awaited.origin)
            (Direct.promiseRegisterCallback req now) state
        (.promiseRegisterCallback res, next, out)
  | .promiseRegisterListener req =>
      let (res, next, out) :=
        runDocument config (.origin req.awaited.origin)
          (Direct.promiseRegisterListener req now) state
      (.promiseRegisterListener res, next, out)
  | .promiseSearch req =>
      pureRequest (.promiseSearch (Direct.promiseSearch req now)) state
  | .scheduleGet req =>
      let (res, next, out) :=
        runDocument config (.schedule req.id)
          (Direct.scheduleGet req now) state
      (.scheduleGet res, next, out)
  | .scheduleCreate req =>
      let (res, next, out) :=
        runDocument config (.schedule req.id)
          (Direct.scheduleCreate req now) state
      (.scheduleCreate res, next, out)
  | .scheduleDelete req =>
      let (res, next, out) :=
        runDocument config (.schedule req.id)
          (Direct.scheduleDelete req now) state
      (.scheduleDelete res, next, out)
  | .scheduleSearch req =>
      pureRequest (.scheduleSearch (Direct.scheduleSearch req now)) state
  | .taskGet req =>
      let (res, next, out) :=
        runDocument config (.origin req.id.origin)
          (Direct.taskGet req now) state
      (.taskGet res, next, out)
  | .taskCreate req =>
      let (res, next, out) :=
        runDocument config (.origin req.action.id.origin)
          (Direct.taskCreate req now) state
      (.taskCreate res, next, out)
  | .taskAcquire req =>
      let (res, next, out) :=
        runDocument config (.origin req.id.origin)
          (Direct.taskAcquire req now) state
      (.taskAcquire res, next, out)
  | .taskFence req =>
      if !req.action.targetId.sameOrigin req.id then
        pureRequest (.taskFence { status := 400 }) state
      else
        let (res, next, out) :=
          runDocument config (.origin req.id.origin)
            (Direct.taskFence req now) state
        (.taskFence res, next, out)
  | .taskHeartbeat req =>
      match req.tasks with
      | [] => pureRequest (.taskHeartbeat { status := 200 }) state
      | first :: _ =>
          if sameOriginRefs first.id.origin req.tasks then
            let (res, next, out) :=
              runDocument config (.origin first.id.origin)
                (Direct.taskHeartbeat first.id.origin req now) state
            (.taskHeartbeat res, next, out)
          else
            pureRequest (.taskHeartbeat { status := 400 }) state
  | .taskSuspend req =>
      if req.actions.any (fun action =>
          !action.awaited.sameOrigin req.id) then
        pureRequest (.taskSuspend { status := 400 }) state
      else
        let (res, next, out) :=
          runDocument config (.origin req.id.origin)
            (Direct.taskSuspend req now) state
        (.taskSuspend res, next, out)
  | .taskFulfill req =>
      if !req.action.id.sameOrigin req.id then
        pureRequest (.taskFulfill { status := 400 }) state
      else
        let (res, next, out) :=
          runDocument config (.origin req.id.origin)
            (Direct.taskFulfill req now) state
        (.taskFulfill res, next, out)
  | .taskRelease req =>
      let (res, next, out) :=
        runDocument config (.origin req.id.origin)
          (Direct.taskRelease req now) state
      (.taskRelease res, next, out)
  | .taskHalt req =>
      let (res, next, out) :=
        runDocument config (.origin req.id.origin)
          (Direct.taskHalt req now) state
      (.taskHalt res, next, out)
  | .taskContinue req =>
      let (res, next, out) :=
        runDocument config (.origin req.id.origin)
          (Direct.taskContinue req now) state
      (.taskContinue res, next, out)
  | .taskSearch req =>
      pureRequest (.taskSearch (Direct.taskSearch req now)) state

/-- Every external process step is pure or commits one indexed document. -/
theorem handleExternal_atMostOneDocument (config : Config) (request : Request)
    (now : Time) (state : State) :
    Direct.Store.AtMostOneDocument state.store
      (handleExternal config request now state).2.1.store := by
  cases request with
  | promiseGet req =>
      simpa [handleExternal] using
        runDocument_atMostOne config (.origin req.id.origin)
          (Direct.promiseGet req now) state
  | promiseCreate req =>
      simpa [handleExternal] using
        runDocument_atMostOne config (.origin req.id.origin)
          (Direct.promiseCreate req now) state
  | promiseSettle req =>
      simpa [handleExternal] using
        runDocument_atMostOne config (.origin req.id.origin)
          (Direct.promiseSettle req now) state
  | promiseRegisterCallback req =>
      simp only [handleExternal]
      split
      · left; intro key; rfl
      · exact runDocument_atMostOne config (.origin req.awaited.origin)
          (Direct.promiseRegisterCallback req now) state
  | promiseRegisterListener req =>
      simpa [handleExternal] using
        runDocument_atMostOne config (.origin req.awaited.origin)
          (Direct.promiseRegisterListener req now) state
  | promiseSearch _ => left; intro key; rfl
  | scheduleGet req =>
      simpa [handleExternal] using
        runDocument_atMostOne config (.schedule req.id)
          (Direct.scheduleGet req now) state
  | scheduleCreate req =>
      simpa [handleExternal] using
        runDocument_atMostOne config (.schedule req.id)
          (Direct.scheduleCreate req now) state
  | scheduleDelete req =>
      simpa [handleExternal] using
        runDocument_atMostOne config (.schedule req.id)
          (Direct.scheduleDelete req now) state
  | scheduleSearch _ => left; intro key; rfl
  | taskGet req =>
      simpa [handleExternal] using
        runDocument_atMostOne config (.origin req.id.origin)
          (Direct.taskGet req now) state
  | taskCreate req =>
      simpa [handleExternal] using
        runDocument_atMostOne config (.origin req.action.id.origin)
          (Direct.taskCreate req now) state
  | taskAcquire req =>
      simpa [handleExternal] using
        runDocument_atMostOne config (.origin req.id.origin)
          (Direct.taskAcquire req now) state
  | taskFence req =>
      simp only [handleExternal]
      split
      · left; intro key; rfl
      · exact runDocument_atMostOne config (.origin req.id.origin)
          (Direct.taskFence req now) state
  | taskHeartbeat req =>
      obtain ⟨pid, tasks⟩ := req
      cases tasks with
      | nil => left; intro key; rfl
      | cons first rest =>
          simp only [handleExternal]
          split
          · exact runDocument_atMostOne config (.origin first.id.origin)
              (Direct.taskHeartbeat first.id.origin
                { pid, tasks := first :: rest } now) state
          · left; intro key; rfl
  | taskSuspend req =>
      simp only [handleExternal]
      split
      · left; intro key; rfl
      · exact runDocument_atMostOne config (.origin req.id.origin)
          (Direct.taskSuspend req now) state
  | taskFulfill req =>
      simp only [handleExternal]
      split
      · left; intro key; rfl
      · exact runDocument_atMostOne config (.origin req.id.origin)
          (Direct.taskFulfill req now) state
  | taskRelease req =>
      simpa [handleExternal] using
        runDocument_atMostOne config (.origin req.id.origin)
          (Direct.taskRelease req now) state
  | taskHalt req =>
      simpa [handleExternal] using
        runDocument_atMostOne config (.origin req.id.origin)
          (Direct.taskHalt req now) state
  | taskContinue req =>
      simpa [handleExternal] using
        runDocument_atMostOne config (.origin req.id.origin)
          (Direct.taskContinue req now) state
  | taskSearch _ => left; intro key; rfl

/-- Apply one of all 21 external operations at the request timestamp. -/
def run (config : Config) (call : Call) (state : State) :
    State × List Output :=
  let (response, next, emitted) :=
    handleExternal config call.request call.requestedAt state
  (next, .response call.client call.id response ::
    emitted.map .message)

/-- Unreliable infrastructure may reject a request before its transaction. -/
def runShed (call : Call) (state : State) : State × List Output :=
  (state, [unavailable call])

/-- A transaction may commit while the serving node loses its selected reply
and returns only an unavailable response. Writer emissions are retained in the
abstract network; the concrete environment may delay or never observe them. -/
def runLose (config : Config) (call : Call) (state : State) :
    State × List Output :=
  let result := run config call state
  (result.1, unavailable call :: result.2.drop 1)

theorem run_atMostOneDocument (config : Config) (call : Call)
    (state : State) :
    Direct.Store.AtMostOneDocument state.store
      (run config call state).1.store := by
  simpa [run] using
    handleExternal_atMostOneDocument config call.request call.requestedAt state

def occurrenceEntry (fallback : Time) (work : WorkItem) : WorkflowEntry :=
  match work with
  | .occurrence _ time => .work work time
  | _ => .work work fallback

def runWork (config : Config) (work : WorkItem) (now : Time)
    (rest : List WorkflowEntry) (state : State) : State × List Output :=
  match work with
  | .promiseTimeout id =>
      let (_, next, emitted) :=
        runDocument config (.origin id.origin)
          (Direct.processPromiseTimeout id now) state
      ({ next with workflow := { pending := rest } }, emitted.map .message)
  | .callback req =>
      let (_, next, emitted) :=
        runDocument config (.origin req.awaited.origin)
          (Direct.processCallback req now) state
      ({ next with workflow := { pending := rest } }, emitted.map .message)
  | .listener req =>
      let (_, next, emitted) :=
        runDocument config (.origin req.awaited.origin)
          (Direct.processListener req now) state
      ({ next with workflow := { pending := rest } }, emitted.map .message)
  | .taskLeaseTimeout id =>
      let (_, next, emitted) :=
        runDocument config (.origin id.origin)
          (Direct.processLeaseTimeout id now) state
      ({ next with workflow := { pending := rest } }, emitted.map .message)
  | .taskRetryTimeout id =>
      let (_, next, emitted) :=
        runDocument config (.origin id.origin)
          (Direct.processRetryTimeout id now) state
      ({ next with workflow := { pending := rest } }, emitted.map .message)
  | .scheduleTimeout id =>
      let (occurrences, next, emitted) :=
        runDocument config (.schedule id)
          (Direct.processSchedule id now) state
      ({ next with workflow := {
          pending := rest ++ occurrences.map (occurrenceEntry now) } },
        emitted.map .message)
  | .occurrence req time =>
      let (_, next, emitted) :=
        runDocument config (.origin req.id.origin)
          (Direct.processOccurrence req time) state
      ({ next with workflow := { pending := rest } }, emitted.map .message)

/-- A timeout work step frames every document except its statically selected
key, including schedule/occurrence continuation steps. -/
theorem runWork_frame (config : Config) (work : WorkItem) (now : Time)
    (rest : List WorkflowEntry) (state : State) (other : DocumentKey)
    (h : other ≠ work.key) :
    (runWork config work now rest state).1.store.read other =
      state.store.read other := by
  cases work <;>
    simp only [WorkItem.key] at h <;>
    simp [runWork, runDocument, Direct.runWith, h]

/-- Compatibility entry point for one named internal operation. Schedule
operations only update their schedule document and queue occurrence
continuations. -/
def runInternal (config : Config) (step : InternalStep) (now : Time)
    (state : State) : State × List Output :=
  let work :=
    match step with
    | .promiseTimeout req => WorkItem.promiseTimeout req.id
    | .callback req => .callback req
    | .listener req => .listener req
    | .taskLeaseTimeout req => .taskLeaseTimeout req.id
    | .taskRetryTimeout req => .taskRetryTimeout req.id
    | .scheduleTimeout req => .scheduleTimeout req.schedule
  runWork config work now state.workflow.pending state

/-- Execute one captured document scan. Origin work is snapshotted and
processed in one origin-document transaction. A schedule transaction appends
separate occurrence-origin continuations. -/
def runScan (config : Config) (key : DocumentKey) (instant : Time)
    (rest : List WorkflowEntry) (state : State) : State × List Output :=
  match key with
  | .origin origin =>
      let (_, next, emitted) :=
        runDocument config (.origin origin)
          (Direct.processOriginScan origin instant) state
      ({ next with workflow := { pending := rest } }, emitted.map .message)
  | .schedule id =>
      let (occurrences, next, emitted) :=
        runDocument config (.schedule id)
          (Direct.processSchedule id instant) state
      ({ next with workflow := {
          pending := rest ++ occurrences.map (occurrenceEntry instant) } },
        emitted.map .message)

theorem runScan_frame (config : Config) (key : DocumentKey) (instant : Time)
    (rest : List WorkflowEntry) (state : State) (other : DocumentKey)
    (h : other ≠ key) :
    (runScan config key instant rest state).1.store.read other =
      state.store.read other := by
  cases key <;>
    simp [runScan, runDocument, Direct.runWith, h]

def runWorkflowEntry (config : Config) (entry : WorkflowEntry)
    (rest : List WorkflowEntry) (state : State) : State × List Output :=
  match entry with
  | .scan key instant => runScan config key instant rest state
  | .work item instant => runWork config item instant rest state

/-- An idle timeout captures only a current key as a finite scan cursor. A
later timeout reads and processes that key's then-current document at the
captured semantic instant. -/
def runTimeout (config : Config) (now : Time) (state : State) :
    State × List Output :=
  match state.workflow.pending with
  | entry :: rest => runWorkflowEntry config entry rest state
  | [] =>
      match state.store.keys with
      | [] => (state, [])
      | key :: _ =>
          ({ state with workflow := {
            pending := [.scan key now] } }, [])

/-- A concrete node can know only keys whose writes were acknowledged. The
abstract machine therefore permits an idle timeout to retain an empty cursor
or capture any one current key. No document is inspected in this step. -/
def runTimeoutChoices (config : Config) (now : Time) (state : State) :
    Outcomes (State × List Output) :=
  match state.workflow.pending with
  | entry :: rest =>
      Outcomes.one (runWorkflowEntry config entry rest state)
  | [] =>
      ⟨(state, []) ::
          state.store.keys.map fun key =>
            ({ state with workflow := {
              pending := [.scan key now] } }, []),
        by simp⟩

theorem runTimeout_mem_choices (config : Config) (now : Time)
    (state : State) :
    runTimeout config now state ∈ (runTimeoutChoices config now state).val := by
  cases hp : state.workflow.pending with
  | nil =>
      cases hk : state.store.keys with
      | nil => simp [runTimeout, runTimeoutChoices, hp, hk]
      | cons key rest =>
          simp [runTimeout, runTimeoutChoices, hp, hk]
  | cons entry rest =>
      simp [runTimeout, runTimeoutChoices, hp, Outcomes.one]

/-- Every timeout process step either leaves all documents unchanged or frames
all but one key. Local workflow advancement does not weaken this store frame. -/
theorem runTimeout_atMostOneDocument (config : Config) (now : Time)
    (state : State) :
    Direct.Store.AtMostOneDocument state.store
      (runTimeout config now state).1.store := by
  cases hp : state.workflow.pending with
  | nil =>
      cases hk : state.store.keys with
      | nil =>
          left
          intro other
          simp [runTimeout, hp, hk]
      | cons key tail =>
          left
          intro other
          simp [runTimeout, hp, hk]
  | cons entry rest =>
      right
      refine ⟨entry.key, ?_⟩
      intro other h
      cases entry with
      | scan key instant =>
          simpa [runTimeout, hp, runWorkflowEntry, WorkflowEntry.key] using
            runScan_frame config key instant rest state other h
      | work item instant =>
          simpa [runTimeout, hp, runWorkflowEntry, WorkflowEntry.key] using
            runWork_frame config item instant rest state other h

end Resonate

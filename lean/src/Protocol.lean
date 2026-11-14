import Rover
import «02-abstract».«system»

/-!
# Shared Resonate protocol

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
abbrev PromiseObject := AbstractModel.PromiseObject
abbrev TaskObject := AbstractModel.TaskObject
abbrev ServerConfig := AbstractModel.ServerConfig

/-- Pure environment value supplied to document decision functions. -/
structure HandlerEnv where
  config : ServerConfig := {}

deriving instance DecidableEq for Value
deriving instance DecidableEq for PromiseRecord
deriving instance DecidableEq for TaskRecord
deriving instance DecidableEq for Schedule
deriving instance DecidableEq for ServerModel.Message
deriving instance DecidableEq for OutboxEntry

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

/-- Runtime settings shared by the two implementations.  This is protocol
configuration, not an abstract transition. -/
structure Config extends ServerConfig where
  deriving Repr

/-- One promise and the task that executes it, addressed by its id. -/
structure Object where
  id : Ident
  promise : PromiseObject
  task : Option TaskObject := none
  deriving Repr

/-- The abstract system: a list of promise/task objects and a list of
schedules. -/
structure Store where
  objects : List Object := []
  schedules : List Schedule := []

/-- Internal work values are shared data.  Their trace is implementation
specific. -/
inductive WorkItem where
  | promiseTimeout (id : ServerModel.Ident)
  | callback (req : PromiseRegisterCallbackReq)
  | listener (req : PromiseRegisterListenerReq)
  | taskLeaseTimeout (id : ServerModel.Ident)
  | taskRetryTimeout (id : ServerModel.Ident)
  | scheduleTimeout (id : ServerModel.Ident)
  | occurrence (req : PromiseCreateReq) (time : Nat)
  deriving Repr

/-- Cross-document schedule occurrence continuation data. -/
structure WorkflowEntry where
  request : PromiseCreateReq
  instant : Nat
  deriving Repr

def WorkflowEntry.item (entry : WorkflowEntry) : WorkItem :=
  .occurrence entry.request entry.instant

/-- Local continuation state shared as a value shape; each implementation
decides independently how transitions update it. -/
structure WorkflowState where
  pending : List WorkflowEntry := []
  deriving Repr

/-- The abstract service state: one list of promise/task rows, one list of
schedules, and the local workflow queue. -/
structure State where
  store : Store := {}
  workflow : WorkflowState := {}

def State.objects (state : State) : List Object :=
  state.store.objects

def State.schedules (state : State) : List Schedule :=
  state.store.schedules

def State.init : State := {}

def sameOriginRefs (origin : String) (refs : List TaskRef) : Bool :=
  refs.all (·.id.origin == origin)

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

end Resonate

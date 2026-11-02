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

/-- A document transaction key. -/
inductive DocumentKey where
  | origin (origin : String)
  | schedule (id : ServerModel.Ident)
  deriving Repr, DecidableEq

/-- A fused promise/task row.  The index prevents storing an id from another
origin in this document. -/
structure OriginObject (origin : String) where
  suffix : String
  promise : PromiseObject
  task : Option TaskObject := none
  deriving Repr

def OriginObject.id (object : OriginObject origin) : ServerModel.Ident :=
  { origin, suffix := object.suffix }

/-- Pure read projection at a logical time. -/
def OriginObject.project (object : OriginObject origin) (now : Nat) :
    OriginObject origin :=
  let promise := object.promise.project now
  { object with promise, task := object.task.map (·.view promise) }

abbrev OriginDocument (origin : String) := List (OriginObject origin)

/-- Schedule contents omit the id because it is fixed by the index. -/
structure ScheduleData (id : ServerModel.Ident) where
  cron : String
  promiseId : ServerModel.Ident
  promiseTimeout : Nat
  promiseParam : Value
  promiseTags : Tags
  nextRunAt : Nat
  lastRunAt : Option Nat := none
  createdAt : Nat
  deriving Repr

def ScheduleData.toSchedule {id : ServerModel.Ident}
    (data : ScheduleData id) : Schedule :=
  { id
    cron := data.cron
    promiseId := data.promiseId
    promiseTimeout := data.promiseTimeout
    promiseParam := data.promiseParam
    promiseTags := data.promiseTags
    nextRunAt := data.nextRunAt
    lastRunAt := data.lastRunAt
    createdAt := data.createdAt }

def ScheduleData.ofSchedule (schedule : Schedule) :
    ScheduleData schedule.id :=
  { cron := schedule.cron
    promiseId := schedule.promiseId
    promiseTimeout := schedule.promiseTimeout
    promiseParam := schedule.promiseParam
    promiseTags := schedule.promiseTags
    nextRunAt := schedule.nextRunAt
    lastRunAt := schedule.lastRunAt
    createdAt := schedule.createdAt }

abbrev ScheduleDocument (id : ServerModel.Ident) := Option (ScheduleData id)

/-- Public dependent document value family. -/
def Document : DocumentKey → Type
  | .origin origin => OriginDocument origin
  | .schedule id => ScheduleDocument id

def emptyDocument : (key : DocumentKey) → Document key
  | .origin _ => []
  | .schedule _ => none

/-- Generic pure Reader/State/Writer plumbing for one indexed document.
It contains no request or timeout transition logic. -/
def DocumentHandler (key : DocumentKey) (α : Type) : Type :=
  HandlerEnv → Document key → α × Document key × List OutboxEntry

instance (key : DocumentKey) : Monad (DocumentHandler key) where
  pure value := fun _ document => (value, document, [])
  bind action next := fun env document =>
    let (value, document', emitted₁) := action env document
    let (result, document'', emitted₂) := next value env document'
    (result, document'', emitted₁ ++ emitted₂)

def documentAsk {key : DocumentKey} : DocumentHandler key HandlerEnv :=
  fun env document => (env, document, [])

def documentGet {key : DocumentKey} : DocumentHandler key (Document key) :=
  fun _ document => (document, document, [])

def documentSet {key : DocumentKey} (document : Document key) :
    DocumentHandler key Unit :=
  fun _ _ => ((), document, [])

def documentModify {key : DocumentKey} (f : Document key → Document key) :
    DocumentHandler key Unit :=
  fun _ document => ((), f document, [])

def documentEmit {key : DocumentKey} (entry : OutboxEntry) :
    DocumentHandler key Unit :=
  fun _ document => ((), document, [entry])

/-- Pure finite dependent document map shared by the specifications. -/
structure Store where
  keys : List DocumentKey := []
  documents : (key : DocumentKey) → Document key := emptyDocument

def Store.read (store : Store) (key : DocumentKey) : Document key :=
  store.documents key

def Store.write (store : Store) (key : DocumentKey) (document : Document key) :
    Store :=
  { keys :=
      if store.keys.contains key then store.keys else store.keys ++ [key]
    documents := fun other =>
      if h : other = key then h.symm ▸ document else store.documents other }

@[simp] theorem Store.read_write_same (store : Store) (key : DocumentKey)
    (document : Document key) :
    (store.write key document).read key = document := by
  simp [Store.write, Store.read]

@[simp] theorem Store.read_write_other (store : Store) (key other : DocumentKey)
    (document : Document key) (h : other ≠ key) :
    (store.write key document).read other = store.read other := by
  simp [Store.write, Store.read, h]

@[simp] theorem Store.key_mem_write (store : Store) (key : DocumentKey)
    (document : Document key) :
    key ∈ (store.write key document).keys := by
  by_cases h : key ∈ store.keys <;> simp [Store.write, h]

def Store.originKeys (store : Store) : List String :=
  store.keys.filterMap fun
    | .origin origin => some origin
    | .schedule _ => none

def Store.scheduleKeys (store : Store) : List ServerModel.Ident :=
  store.keys.filterMap fun
    | .origin _ => none
    | .schedule id => some id

/-- Internal work values are shared data.  Their execution is implementation
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

def WorkItem.key : WorkItem → DocumentKey
  | .promiseTimeout id => .origin id.origin
  | .callback req => .origin req.awaited.origin
  | .listener req => .origin req.awaited.origin
  | .taskLeaseTimeout id => .origin id.origin
  | .taskRetryTimeout id => .origin id.origin
  | .scheduleTimeout id => .schedule id
  | .occurrence req _ => .origin req.id.origin

/-- Cross-document schedule occurrence continuation data. -/
structure WorkflowEntry where
  request : PromiseCreateReq
  instant : Nat
  deriving Repr

def WorkflowEntry.item (entry : WorkflowEntry) : WorkItem :=
  .occurrence entry.request entry.instant

def WorkflowEntry.key (entry : WorkflowEntry) : DocumentKey :=
  .origin entry.request.id.origin

/-- Local continuation state shared as a value shape; each implementation
decides independently how transitions update it. -/
structure WorkflowState where
  pending : List WorkflowEntry := []
  deriving Repr

/-- Logical document state used to state cross-implementation correspondence. -/
structure State where
  store : Store := {}
  workflow : WorkflowState := {}

def State.init : State := {}

def State.originDocument (state : State) (origin : String) :
    OriginDocument origin :=
  state.store.read (.origin origin)

def State.scheduleDocument (state : State) (id : ServerModel.Ident) :
    ScheduleDocument id :=
  state.store.read (.schedule id)

def State.withOrigin (state : State) (origin : String)
    (document : OriginDocument origin) : State :=
  { state with store := state.store.write (.origin origin) document }

def State.withSchedule (state : State) (schedule : Schedule) : State :=
  { state with
    store := state.store.write (.schedule schedule.id)
      (some (ScheduleData.ofSchedule schedule)) }

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

import Rover.World
import Resonate.Internal

/-!
# Full Resonate protocol and direct abstract semantics

The request, response, record, schedule, task, and outbox payloads below are
the public types from the pinned `resonatehq/resonate` specification.  Rover
adds only transport envelopes and request correlation.
-/

namespace Resonate

open Rover
open ServerModel

abbrev Addr := String
abbrev CallId := Nat
abbrev Request := Equivalence.Request
abbrev Response := Equivalence.Response
abbrev InternalStep := Abstraction.InternalStep
abbrev State := Direct.ServerState
abbrev Config := Direct.ServerConfig

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

/-- Publicly observable emissions: correlated replies and outbox messages. -/
inductive Output where
  | response (client : Addr) (id : CallId) (response : Response)
  | message (entry : OutboxEntry)
  deriving Repr, BEq, DecidableEq

/-- Internal work is a real process-local message, but is not injectable. -/
inductive Message where
  | request (call : Call)
  | internal (step : InternalStep)
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

def handleExternal (request : Request) (now : Time) : Direct.H Response :=
  match request with
  | .promiseGet req => .promiseGet <$> Direct.promiseGet req now
  | .promiseCreate req => .promiseCreate <$> Direct.promiseCreate req now
  | .promiseSettle req => .promiseSettle <$> Direct.promiseSettle req now
  | .promiseRegisterCallback req =>
      .promiseRegisterCallback <$> Direct.promiseRegisterCallback req now
  | .promiseRegisterListener req =>
      .promiseRegisterListener <$> Direct.promiseRegisterListener req now
  | .promiseSearch req => .promiseSearch <$> Direct.promiseSearch req now
  | .scheduleGet req => .scheduleGet <$> Direct.scheduleGet req now
  | .scheduleCreate req => .scheduleCreate <$> Direct.scheduleCreate req now
  | .scheduleDelete req => .scheduleDelete <$> Direct.scheduleDelete req now
  | .scheduleSearch req => .scheduleSearch <$> Direct.scheduleSearch req now
  | .taskGet req => .taskGet <$> Direct.taskGet req now
  | .taskCreate req => .taskCreate <$> Direct.taskCreate req now
  | .taskAcquire req => .taskAcquire <$> Direct.taskAcquire req now
  | .taskFence req => .taskFence <$> Direct.taskFence req now
  | .taskHeartbeat req => .taskHeartbeat <$> Direct.taskHeartbeat req now
  | .taskSuspend req => .taskSuspend <$> Direct.taskSuspend req now
  | .taskFulfill req => .taskFulfill <$> Direct.taskFulfill req now
  | .taskRelease req => .taskRelease <$> Direct.taskRelease req now
  | .taskHalt req => .taskHalt <$> Direct.taskHalt req now
  | .taskContinue req => .taskContinue <$> Direct.taskContinue req now
  | .taskSearch req => .taskSearch <$> Direct.taskSearch req now

/-- Entries newly inserted or replaced by one atomic transition. -/
def outboxDelta (before after : State) : List OutboxEntry :=
  after.outbox.filter fun entry =>
    !(before.outbox.any fun old => old == entry)

def transitionOutputs (before after : State) : List Output :=
  (outboxDelta before after).map .message

/-- Apply one of all 21 external handlers at the request's own timestamp. -/
def run (config : Config) (call : Call) (state : State) :
    State × List Output :=
  let (response, next) :=
    Direct.runWith config (handleExternal call.request call.requestedAt) state
  (next, .response call.client call.id response ::
    transitionOutputs state next)

/-- Apply one of all six process-local handlers at the Rover step time. -/
def runInternal (config : Config) (step : InternalStep) (now : Time)
    (state : State) : State × List Output :=
  let (_, next) :=
    Direct.runWith config (Direct.handleInternal step now) state
  (next, transitionOutputs state next)

end Resonate

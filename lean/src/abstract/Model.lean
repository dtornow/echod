import «abstract».Internal

/-!
# Abstract Resonate

There is exactly one real process. Its state is a list of objects (a promise
and its task), a list of schedules, and a queue of schedule occurrences. A
request or a timeout reads the objects it names and writes back the ones it
changes. Emitted messages go directly to Rover's network.
-/

namespace Resonate.Abstract

open Rover
open ServerModel

/-- One workflow request transition: drain old due work, run the public
handler, then drain work made due by that handler. -/
def completeOrigin (origin : String) (now : Time)
    (action : Handler α) : Handler α := do
  sweepOrigin origin now
  let result ← action
  sweepOrigin origin now
  return result

/-- The handler for each of the 21 public operations. -/
def handler (request : Request) (now : Time) : Handler Response :=
  match request with
  | .promiseGet req =>
      .promiseGet <$> completeOrigin req.id.origin now (promiseGet req now)
  | .promiseCreate req =>
      .promiseCreate <$> completeOrigin req.id.origin now (promiseCreate req now)
  | .promiseSettle req =>
      .promiseSettle <$> completeOrigin req.id.origin now (promiseSettle req now)
  | .promiseRegisterCallback req =>
      if req.awaited.sameOrigin req.awaiter then
        .promiseRegisterCallback <$>
          completeOrigin req.awaited.origin now (promiseRegisterCallback req now)
      else
        .promiseRegisterCallback <$> promiseRegisterCallback req now
  | .promiseRegisterListener req =>
      .promiseRegisterListener <$>
        completeOrigin req.awaited.origin now (promiseRegisterListener req now)
  | .promiseSearch req => pure (.promiseSearch (promiseSearch req now))
  | .scheduleGet req => .scheduleGet <$> scheduleGet req now
  | .scheduleCreate req => .scheduleCreate <$> scheduleCreate req now
  | .scheduleDelete req => .scheduleDelete <$> scheduleDelete req now
  | .scheduleSearch req => pure (.scheduleSearch (scheduleSearch req now))
  | .taskGet req =>
      .taskGet <$> completeOrigin req.id.origin now (taskGet req now)
  | .taskCreate req =>
      .taskCreate <$> completeOrigin req.action.id.origin now (taskCreate req now)
  | .taskAcquire req =>
      .taskAcquire <$> completeOrigin req.id.origin now (taskAcquire req now)
  | .taskFence req =>
      if req.action.targetId != req.id ∧ req.action.targetId.sameOrigin req.id then
        .taskFence <$> completeOrigin req.id.origin now (taskFence req now)
      else
        .taskFence <$> taskFence req now
  | .taskHeartbeat req =>
      match req.tasks with
      | [] => .taskHeartbeat <$> taskHeartbeat req now
      | first :: _ =>
          if sameOriginRefs first.id.origin req.tasks then
            .taskHeartbeat <$>
              completeOrigin first.id.origin now (taskHeartbeat req now)
          else
            .taskHeartbeat <$> taskHeartbeat req now
  | .taskSuspend req =>
      if req.actions.any (fun action => !action.awaited.sameOrigin req.id) then
        .taskSuspend <$> taskSuspend req now
      else
        .taskSuspend <$> completeOrigin req.id.origin now (taskSuspend req now)
  | .taskFulfill req =>
      if req.action.id.sameOrigin req.id then
        .taskFulfill <$> completeOrigin req.id.origin now (taskFulfill req now)
      else
        .taskFulfill <$> taskFulfill req now
  | .taskRelease req =>
      .taskRelease <$> completeOrigin req.id.origin now (taskRelease req now)
  | .taskHalt req =>
      .taskHalt <$> completeOrigin req.id.origin now (taskHalt req now)
  | .taskContinue req =>
      .taskContinue <$> completeOrigin req.id.origin now (taskContinue req now)
  | .taskSearch req => pure (.taskSearch (taskSearch req now))

/-- Run the request's handler: its response, the next state, and the
messages it emitted. -/
def serve (config : Config) (call : Call) (state : State) :
    Response × State × List Output :=
  let (response, store, emitted) :=
    handler call.request call.requestedAt { config := config.toServerConfig }
      state.store
  (response, { state with store }, emitted.map .message)

/-- Serve one request: reply, and send what it emitted. -/
def run (config : Config) (call : Call) (state : State) :
    State × List Output :=
  let (response, next, sent) := serve config call state
  (next, .response call.client call.id response :: sent)

/-- Unreliable infrastructure may reject a request before it runs. -/
def runShed (call : Call) (state : State) : State × List Output :=
  (state, [unavailable call])

/-- The request runs, but the reply is lost and the client sees
unavailable. Emitted messages are still sent. -/
def runLose (config : Config) (call : Call) (state : State) :
    State × List Output :=
  let (_, next, sent) := serve config call state
  (next, unavailable call :: sent)

/-- Run one piece of due work. `rest` is the continuation queue without it;
a schedule appends the occurrences it fired. -/
def runWork (config : Config) (work : WorkItem) (now : Time)
    (rest : List WorkflowEntry) (state : State) : State × List Output :=
  let (fired, store, emitted) :=
    processWork work now { config := config.toServerConfig } state.store
  ({ store, workflow := { pending := rest ++ fired } }, emitted.map .message)

/-- Work a timeout may run: any queued occurrence, or any step of an object
or schedule at any instant up to `now`. Each comes with its instant and the
queue left once it runs. -/
def timeoutWork (state : State) (now : Time) :
    List (WorkItem × Time × List WorkflowEntry) :=
  let queue := state.workflow.pending
  queue.mapIdx (fun index entry => (entry.item, entry.instant, queue.eraseIdx index)) ++
  (List.range (now + 1)).flatMap fun instant =>
    (state.store.objects.flatMap objectWork ++
      state.store.schedules.map (fun schedule => WorkItem.scheduleTimeout schedule.id)).map
        fun item => (item, instant, queue)

/-- A timeout does nothing or runs any internal step. A step that is not due
does nothing. -/
def runTimeout (config : Config) (now : Time) (state : State) :
    Outcomes (State × List Output) :=
  ⟨(state, []) :: (timeoutWork state now).map
      (fun (item, instant, rest) => runWork config item instant rest state),
    by simp⟩

inductive Pid where
  | outside
  | service
  deriving DecidableEq, Repr

def sends (outputs : List Output) : List (Pid × Message) :=
  outputs.map fun output => (Pid.outside, Message.output output)

def step (config : Config) (pid : Pid) (state : State) (now : Time)
    (event : Event Pid Message) : Outcomes (Result Pid State Message) :=
  match pid, event with
  | .service, .receive .outside (.request call) =>
      let served := run config call state
      let lost := runLose config call state
      let shed := runShed call state
      ⟨[
        { state := served.1, send := sends served.2 },
        { state := lost.1, send := sends lost.2 },
        { state := shed.1, send := sends shed.2 }
      ], by simp⟩
  | .service, .timeout =>
      let choices := runTimeout config now state
      ⟨choices.val.map fun (next, outputs) =>
          { state := next, send := sends outputs },
        by
          obtain ⟨head, tail, h⟩ :=
            List.exists_cons_of_ne_nil choices.property
          rw [h]
          simp⟩
  | _, _ => Outcomes.one { state := state, send := [] }

abbrev model : Model where
  Config := Config
  Pid := Pid
  State := State
  Msg := Message
  decEqPid := inferInstance
  outside := .outside
  isProcess := (· = .service)
  decIsProcess := inferInstance
  outside_not_process := by simp
  injectable := fun _ message => ∃ call, message = .request call
  decInjectable := by
    intro _ message
    cases message with
    | request call => exact isTrue ⟨call, rfl⟩
    | output output =>
        exact isFalse (by rintro ⟨call, h⟩; contradiction)
  init := fun _ process => process = fun _ => State.init
  step := step

theorem only_real_process {pid : Pid} (h : model.isProcess pid) :
    pid = .service := h

def boundaryEvent : Rover.BoundaryEvent model → Option Resonate.BoundaryEvent
  | .input _ time message => message.observeInput time
  | .output _ time message => message.observeOutput time

def boundaryTrace (execution : Execution model) : List Resonate.BoundaryEvent :=
  (Rover.trace execution).filterMap boundaryEvent

def ValidBoundaryTrace (config : Config)
    (events : List Resonate.BoundaryEvent) : Prop :=
  ∃ execution,
    Behavior model config execution ∧
    boundaryTrace execution = events

def initialProcess : Pid → State :=
  fun _ => State.init

theorem initialProcess_valid (config : Config) :
    model.init config initialProcess := rfl

end Resonate.Abstract

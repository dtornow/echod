import «abstract».Internal

/-!
# Abstract Resonate

There is exactly one real process. Its state is a list of objects (a promise
and its task), a list of schedules, and a queue of schedule occurrences. A
request or a timeout reads the objects it names and writes back the ones it
changes. Emitted messages go directly to Rover's network.
-/

namespace Resonate

open Rover
open ServerModel

/-- The handler for each of the 21 public operations. -/
def handler (request : Request) (now : Time) : Abstract.Handler Response :=
  match request with
  | .promiseGet req => .promiseGet <$> Abstract.promiseGet req now
  | .promiseCreate req => .promiseCreate <$> Abstract.promiseCreate req now
  | .promiseSettle req => .promiseSettle <$> Abstract.promiseSettle req now
  | .promiseRegisterCallback req =>
      .promiseRegisterCallback <$> Abstract.promiseRegisterCallback req now
  | .promiseRegisterListener req =>
      .promiseRegisterListener <$> Abstract.promiseRegisterListener req now
  | .promiseSearch req => pure (.promiseSearch (Abstract.promiseSearch req now))
  | .scheduleGet req => .scheduleGet <$> Abstract.scheduleGet req now
  | .scheduleCreate req => .scheduleCreate <$> Abstract.scheduleCreate req now
  | .scheduleDelete req => .scheduleDelete <$> Abstract.scheduleDelete req now
  | .scheduleSearch req => pure (.scheduleSearch (Abstract.scheduleSearch req now))
  | .taskGet req => .taskGet <$> Abstract.taskGet req now
  | .taskCreate req => .taskCreate <$> Abstract.taskCreate req now
  | .taskAcquire req => .taskAcquire <$> Abstract.taskAcquire req now
  | .taskFence req => .taskFence <$> Abstract.taskFence req now
  | .taskHeartbeat req => .taskHeartbeat <$> Abstract.taskHeartbeat req now
  | .taskSuspend req => .taskSuspend <$> Abstract.taskSuspend req now
  | .taskFulfill req => .taskFulfill <$> Abstract.taskFulfill req now
  | .taskRelease req => .taskRelease <$> Abstract.taskRelease req now
  | .taskHalt req => .taskHalt <$> Abstract.taskHalt req now
  | .taskContinue req => .taskContinue <$> Abstract.taskContinue req now
  | .taskSearch req => pure (.taskSearch (Abstract.taskSearch req now))

/-- Serve one request: run its handler, reply, and send what it emitted. -/
def run (config : Config) (call : Call) (state : State) :
    State × List Output :=
  let (response, store, emitted) :=
    handler call.request call.requestedAt { config := config.toServerConfig }
      state.store
  ({ state with store }, .response call.client call.id response ::
    emitted.map .message)

/-- Unreliable infrastructure may reject a request before it runs. -/
def runShed (call : Call) (state : State) : State × List Output :=
  (state, [unavailable call])

/-- The request runs, but the reply is lost and the client sees
unavailable. Emitted messages are still sent. -/
def runLose (config : Config) (call : Call) (state : State) :
    State × List Output :=
  let result := run config call state
  (result.1, unavailable call :: result.2.drop 1)

/-- Run one piece of due work. `rest` is the continuation queue without it;
a schedule appends the occurrences it fired. -/
def runWork (config : Config) (work : WorkItem) (now : Time)
    (rest : List WorkflowEntry) (state : State) : State × List Output :=
  let (fired, store, emitted) :=
    Abstract.processWork work now { config := config.toServerConfig } state.store
  ({ store, workflow := { pending := rest ++ fired } }, emitted.map .message)

/-- Work that is due by `now`: any queued occurrence, or any object or
schedule work due at any instant up to `now`. Each comes with its instant and
the queue left once it runs. -/
def dueWork (state : State) (now : Time) :
    List (WorkItem × Time × List WorkflowEntry) :=
  let queue := state.workflow.pending
  queue.mapIdx (fun index entry => (entry.item, entry.instant, queue.eraseIdx index)) ++
  (List.range (now + 1)).flatMap fun instant =>
    (state.store.objects.flatMap (Abstract.objectWork · instant) ++
      state.store.schedules.flatMap (Abstract.scheduleWork · instant)).map
        fun item => (item, instant, queue)

/-- A timeout does nothing or runs any due work. -/
def runTimeout (config : Config) (now : Time) (state : State) :
    Outcomes (State × List Output) :=
  ⟨(state, []) :: (dueWork state now).map
      (fun (item, instant, rest) => runWork config item instant rest state),
    by simp⟩

end Resonate

namespace Resonate.Abstract

open Rover

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
      let served := Resonate.run config call state
      let lost := Resonate.runLose config call state
      let shed := Resonate.runShed call state
      ⟨[
        { state := served.1, send := sends served.2 },
        { state := lost.1, send := sends lost.2 },
        { state := shed.1, send := sends shed.2 }
      ], by simp⟩
  | .service, .timeout =>
      let choices := Resonate.runTimeout config now state
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

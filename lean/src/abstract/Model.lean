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
def handler (request : Request) (now : Time) : Direct.Handler Response :=
  match request with
  | .promiseGet req => .promiseGet <$> Direct.promiseGet req now
  | .promiseCreate req => .promiseCreate <$> Direct.promiseCreate req now
  | .promiseSettle req => .promiseSettle <$> Direct.promiseSettle req now
  | .promiseRegisterCallback req =>
      .promiseRegisterCallback <$> Direct.promiseRegisterCallback req now
  | .promiseRegisterListener req =>
      .promiseRegisterListener <$> Direct.promiseRegisterListener req now
  | .promiseSearch req => pure (.promiseSearch (Direct.promiseSearch req now))
  | .scheduleGet req => .scheduleGet <$> Direct.scheduleGet req now
  | .scheduleCreate req => .scheduleCreate <$> Direct.scheduleCreate req now
  | .scheduleDelete req => .scheduleDelete <$> Direct.scheduleDelete req now
  | .scheduleSearch req => pure (.scheduleSearch (Direct.scheduleSearch req now))
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
  | .taskSearch req => pure (.taskSearch (Direct.taskSearch req now))

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
    Direct.processWork work now { config := config.toServerConfig } state.store
  ({ store, workflow := { pending := rest ++ fired } }, emitted.map .message)

/-- Work due at `instant`, found by looking at every object and schedule. -/
def eligibleWorkAt (state : State) (instant : Time) : List WorkItem :=
  state.store.objects.flatMap (Direct.objectWork · instant) ++
  state.store.schedules.flatMap (Direct.scheduleWork · instant)

/-- Run a queued occurrence; it leaves the queue. -/
def pendingTimeoutChoices (config : Config) (state : State) :
    List (State × List Output) :=
  state.workflow.pending.mapIdx fun index entry =>
    runWork config entry.item entry.instant
      (state.workflow.pending.eraseIdx index) state

/-- Run any work due at any instant up to `now`. -/
def documentTimeoutChoices (config : Config) (now : Time) (state : State) :
    List (State × List Output) :=
  (List.range (now + 1)).flatMap fun instant =>
    (eligibleWorkAt state instant).map fun item =>
      runWork config item instant state.workflow.pending state

def timeoutChoices (config : Config) (now : Time) (state : State) :
    List (State × List Output) :=
  pendingTimeoutChoices config state ++
    documentTimeoutChoices config now state

/-- A timeout may run any choice or do nothing. -/
def runTimeoutChoices (config : Config) (now : Time) (state : State) :
    Outcomes (State × List Output) :=
  ⟨(state, []) :: timeoutChoices config now state, by simp⟩

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
      let choices := Resonate.runTimeoutChoices config now state
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

import Resonate

/-!
# Abstract Resonate

There is exactly one real process. Its local state is the complete fused
Resonate server state. External requests and process-local internal messages
each execute one direct-state atomic transition.
-/

namespace Resonate.Abstract

open Rover

inductive Pid where
  | outside
  | service
  deriving DecidableEq, Repr

def sends (state : State) (outputs : List Output) : List (Pid × Message) :=
  outputs.map (fun output => (Pid.outside, Message.output output)) ++
    (Direct.internalSteps state).map fun action =>
      (Pid.service, Message.internal action)

def step (config : Config) (pid : Pid) (state : State) (now : Time)
    (event : Event Pid Message) : Outcomes (Result Pid State Message) :=
  match pid, event with
  | .service, .receive .outside (.request call) =>
      let (next, outputs) := Resonate.run config call state
      Outcomes.one { state := next, send := sends next outputs }
  | .service, .receive .service (.internal action) =>
      let (next, outputs) := Resonate.runInternal config action now state
      Outcomes.one { state := next, send := sends next outputs }
  | _, _ => Outcomes.one { state := state, send := [] }

abbrev model : Model where
  Config := Config
  Pid := Pid
  State := State
  Msg := Message
  decEqPid := inferInstance
  outside := .outside
  isProcess := (· = .service)
  outside_not_process := by simp
  injectable := fun _ message => ∃ call, message = .request call
  init := fun _ process => process .service = AbstractModel.ServerState.init
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
  fun _ => AbstractModel.ServerState.init

theorem initialProcess_valid (config : Config) :
    model.init config initialProcess := rfl

end Resonate.Abstract

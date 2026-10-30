import Resonate

/-!
# Abstract Resonate

There is exactly one real process. Its local state is the complete fused
Resonate state of fused objects and schedules. External requests and
deterministic timeout passes each execute one direct-state atomic transition
and send its transient Writer emissions directly into the Rover network.
-/

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
      let (next, outputs) := Resonate.run config call state
      Outcomes.one { state := next, send := sends outputs }
  | .service, .timeout =>
      let (next, outputs) := Resonate.runTimeout config now state
      Outcomes.one { state := next, send := sends outputs }
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
  init := fun _ process => process .service = State.init
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

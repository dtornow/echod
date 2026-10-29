import Rover.Protocol

/-!
# The abstract Rover

There is exactly one real process.  Its local state is the complete promise
state, so a receive is one atomic protocol linearization.
-/

namespace Rover.Abstract

open Protocol

inductive Pid where
  | outside
  | service
  deriving DecidableEq, Repr

def step (config : Config) (pid : Pid) (state : State) (_now : Time)
    (event : Event Pid Message) : Outcomes (Result Pid State Message) :=
  match pid, event with
  | .service, .receive .outside (.request call) =>
      let outcomes := Protocol.run config call state
      ⟨outcomes.val.map fun (next, outputs) =>
          { state := next
            send := outputs.map fun output => (.outside, .output output) },
        by simpa using outcomes.property⟩
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
  init := fun _ process => process .service = {}
  step := step

theorem only_real_process {pid : Pid} (h : model.isProcess pid) :
    pid = .service := h

def boundaryEvent : Rover.BoundaryEvent model → Option Protocol.BoundaryEvent
  | .input _ time message => message.observeInput time
  | .output _ time message => message.observeOutput time

def boundaryTrace (execution : Execution model) : List Protocol.BoundaryEvent :=
  (Rover.trace execution).filterMap boundaryEvent

def ValidBoundaryTrace (config : Config)
    (events : List Protocol.BoundaryEvent) : Prop :=
  ∃ execution,
    Behavior model config execution ∧
    boundaryTrace execution = events

def initialProcess : Pid → State := fun _ => {}

theorem initialProcess_valid (config : Config) :
    model.init config initialProcess := rfl

end Rover.Abstract

import «abstract».System

/-!
# Abstract Resonate

There is exactly one real process. Its state contains a dependent global
document store plus local continuation state. Every external receive executes
at most one origin or schedule document handler. Every timeout stutters or
executes at most one eligible document handler at a bounded logical firing
instant. Schedule occurrences are queued continuations and therefore run in
later timeout steps. Writer emissions go directly to Rover's network and are
not durable state.
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
      let served := Resonate.run config call state
      if config.unreliable then
        let lost := Resonate.runLose config call state
        let shed := Resonate.runShed call state
        ⟨[
          { state := served.1, send := sends served.2 },
          { state := lost.1, send := sends lost.2 },
          { state := shed.1, send := sends shed.2 }
        ], by simp⟩
      else
        Outcomes.one { state := served.1, send := sends served.2 }
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

/-- The two real service-step branches satisfy the global one-document frame. -/
theorem externalProcessStep_atMostOneDocument (config : Config) (call : Call)
    (state : State) :
    Direct.Store.AtMostOneDocument state.store
      (Resonate.run config call state).1.store :=
  Resonate.run_atMostOneDocument config call state

theorem timeoutProcessStep_atMostOneDocument (config : Config) (now : Time)
    (state : State) :
    Direct.Store.AtMostOneDocument state.store
      (Resonate.runTimeout config now state).1.store :=
  Resonate.runTimeout_atMostOneDocument config now state

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

import Rover
import «concrete».ProcessNode

/-!
# Concrete Resonate over a versioned document store

Servers retain continuations locally and exchange only raw GET and conditional
PUT payloads with one store. RPC operation ids live in a separate envelope.
In particular, a PUT does not carry a call, response, handler state, emission,
or proof. Rover's append-only network may redeliver every request and reply;
`takeFlight` makes replies one-shot, while conditional versions make an old
PUT harmless after its first successful landing.
-/

namespace Resonate.Concrete

open Rover

def step (appConfig : Resonate.Config) (config : Config) (pid : Pid)
    (localState : Local) (now : Time) (event : Event Pid Msg) :
    Outcomes (Result Pid Local Msg) :=
  match pid, localState with
  | .node address, .node node => nodeStep appConfig config address node now event
  | .store, .store store => storeStep Local.store config store event
  | _, _ => Outcomes.one { state := localState, send := [] }

abbrev model (nodes : List Addr) (appConfig : Resonate.Config) : Model where
  Config := Config
  Pid := Pid
  State := Local
  Msg := Msg
  decEqPid := inferInstance
  outside := .outside
  isProcess := fun
    | .node address => address ∈ nodes
    | .store => True
    | .outside => False
  decIsProcess := by
    intro pid
    cases pid with
    | outside => exact isFalse (by simp)
    | node address => exact inferInstance
    | store => exact isTrue trivial
  outside_not_process := by simp
  injectable := fun _ message => ∃ call, message = .request call
  decInjectable := by
    intro _ message
    cases message with
    | request call => exact isTrue ⟨call, rfl⟩
    | output output =>
        exact isFalse (by rintro ⟨call, h⟩; contradiction)
    | storeRequest request =>
        exact isFalse (by rintro ⟨call, h⟩; contradiction)
    | storeReply reply =>
        exact isFalse (by rintro ⟨call, h⟩; contradiction)
  init := fun _ process =>
    nodes.Nodup ∧
    process .store = .store {} ∧
    ∀ address ∈ nodes, process (.node address) = .node {}
  step := step appConfig

def initialProcess : Pid → Local
  | .outside => .outside
  | .node _ => .node {}
  | .store => .store {}

theorem initialProcess_valid (nodes : List Addr)
    (appConfig : Resonate.Config) (config : Config)
    (hnodup : nodes.Nodup) :
    (model nodes appConfig).init config initialProcess := by
  exact ⟨hnodup, rfl, by intros; rfl⟩

def boundaryEvent :
    Rover.BoundaryEvent (model nodes appConfig) →
      Option Resonate.BoundaryEvent
  | .input _ time (.request call) => some (.request time call)
  | .output _ time (.output (.response client id response)) =>
      some (.response time client id response)
  | .output _ time (.output (.message entry)) =>
      some (.message time entry)
  | _ => none

def boundaryTrace (trace : Trace (model nodes appConfig)) :
    List Resonate.BoundaryEvent :=
  (Rover.observe trace).filterMap boundaryEvent

def ValidBoundaryTrace (nodes : List Addr) (appConfig : Resonate.Config)
    (config : Config) (events : List Resonate.BoundaryEvent) : Prop :=
  ∃ trace,
    ValidTrace (model nodes appConfig) config trace ∧
    boundaryTrace trace = events

end Resonate.Concrete

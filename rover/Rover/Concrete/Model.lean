import Rover.Protocol
import Experiment.Storage

/-!
# The concrete Rover

A deployment has any duplicate-free list of server addresses and one object
store. Servers are stateless: they load a snapshot, evaluate the shared
promise transition, and submit a candidate conditional write. The store owns
the durable state and monotonically increasing version.

Because Rover's network is append-only, every load, snapshot, candidate, and
retry may be received repeatedly. A repeated stale candidate conflicts and is
retried; only a candidate matching both the current version and state can
publish its response and notifications.
-/

namespace Rover.Concrete

open Protocol

abbrev Config := Experiment.Storage.Config

inductive Pid where
  | outside
  | server (address : Addr)
  | store
  deriving DecidableEq, Repr

/-- A server-computed state transition, with its semantic justification.
Keeping the witness in the internal message makes the trust boundary explicit:
the object store accepts only candidates produced by the shared protocol. -/
structure Candidate (config : Protocol.Config) where
  call : Call
  before : State
  version : Nat
  after : State
  outputs : List Output
  valid : (after, outputs) ∈ (Protocol.run config call before).val

inductive Msg (config : Protocol.Config) where
  | request (call : Call)
  | output (output : Output)
  | load (call : Call)
  | snapshot (call : Call) (state : State) (version : Nat)
  | cas (candidate : Candidate config)
  | retry (call : Call)

inductive Local where
  | outside
  | node
  | store (state : State) (version : Nat)

def Msg.call? {config : Protocol.Config} : Msg config → Option Call
  | .request call => some call
  | .output _ => none
  | .load call => some call
  | .snapshot call _ _ => some call
  | .cas candidate => some candidate.call
  | .retry call => some call

def candidateResults (config : Protocol.Config) (call : Call)
    (before : State) (version : Nat) :
    Outcomes (Result (Pid) Local (Msg config)) :=
  let outcomes := Protocol.run config call before
  let attached := outcomes.val.attach
  ⟨attached.map fun outcome =>
      { state := .node
        send := [(.store, .cas {
          call := call
          before := before
          version := version
          after := outcome.1.1
          outputs := outcome.1.2
          valid := outcome.2 })] },
    by
      obtain ⟨head, tail, hlist⟩ :=
        List.exists_cons_of_ne_nil outcomes.property
      have hmem : head ∈ outcomes.val := by
        rw [hlist]
        simp
      have hattach :
          (⟨head, hmem⟩ : { value // value ∈ outcomes.val }) ∈ attached := by
        simp [attached]
      exact List.ne_nil_of_mem (List.mem_map_of_mem hattach)⟩

def step (appConfig : Protocol.Config) (config : Config) (pid : Pid)
    (localState : Local) (_now : Time) (event : Event Pid (Msg appConfig)) :
    Outcomes (Result Pid Local (Msg appConfig)) :=
  match pid, localState, event with
  | .server _, .node, .receive .outside (.request call) =>
      Outcomes.one { state := .node, send := [(.store, .load call)] }
  | .server _, .node, .receive .store (.snapshot call state version) =>
      candidateResults appConfig call state version
  | .server _, .node, .receive .store (.retry call) =>
      Outcomes.one { state := .node, send := [(.store, .load call)] }
  | .store, .store state version, .receive (.server server) (.load call) =>
      Outcomes.one {
        state := .store state version
        send := [(.server server, .snapshot call state version)] }
  | .store, .store state version, .receive (.server server) (.cas candidate) =>
      if config.conditional && candidate.version == version &&
          candidate.before == state then
        Outcomes.one {
          state := .store candidate.after (version + 1)
          send := candidate.outputs.map fun output =>
            (.outside, .output output) }
      else
        Outcomes.one {
          state := .store state version
          send := [(.server server, .retry candidate.call)] }
  | _, _, _ => Outcomes.one { state := localState, send := [] }

abbrev model (nodes : List Addr) (appConfig : Protocol.Config) : Model where
  Config := Config
  Pid := Pid
  State := Local
  Msg := Msg appConfig
  decEqPid := inferInstance
  outside := .outside
  isProcess := fun
    | .server address => address ∈ nodes
    | .store => True
    | .outside => False
  outside_not_process := by simp
  injectable := fun _ message => ∃ call, message = .request call
  init := fun _ process =>
    nodes.Nodup ∧
    process .store = .store {} 0 ∧
    ∀ address ∈ nodes, process (.server address) = .node
  step := step appConfig

def initialProcess : Pid → Local
  | .outside => .outside
  | .server _ => .node
  | .store => .store {} 0

theorem initialProcess_valid (nodes : List Addr) (appConfig : Protocol.Config)
    (config : Config) (hnodup : nodes.Nodup) :
    (model nodes appConfig).init config initialProcess := by
  refine ⟨hnodup, rfl, ?_⟩
  intros
  rfl

def boundaryEvent (nodes : List Addr) (appConfig : Protocol.Config) :
    Rover.BoundaryEvent (model nodes appConfig) → Option Protocol.BoundaryEvent
  | .input _ time (.request call) => some (.request time call)
  | .output _ time (.output (.response client id response)) =>
      some (.response time client id response)
  | .output _ time (.output (.notification client record)) =>
      some (.notification time client record)
  | _ => none

def boundaryTrace (nodes : List Addr) (appConfig : Protocol.Config)
    (execution : Execution (model nodes appConfig)) :
    List Protocol.BoundaryEvent :=
  (Rover.trace execution).filterMap (boundaryEvent nodes appConfig)

def ValidBoundaryTrace (nodes : List Addr) (appConfig : Protocol.Config)
    (config : Config) (events : List Protocol.BoundaryEvent) : Prop :=
  ∃ execution,
    Behavior (model nodes appConfig) config execution ∧
    boundaryTrace nodes appConfig execution = events

end Rover.Concrete

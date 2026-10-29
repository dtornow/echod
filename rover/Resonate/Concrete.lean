import Resonate
import Experiment.Storage

/-!
# Concrete Resonate

A deployment has any duplicate-free list of server addresses and one
per-document object store.  The wire protocol is the storage protocol:
`get/got/put/written/conflict/failed`.  In particular, a `put` contains only
its key, document, and expected document version. Operation ids belong to the
RPC envelope, not the application-level request payload. The call and handler
result which justify a write remain in the node's local flight.

Rover's network is append-only, so every request and reply may be delivered
repeatedly. Operation ids let a node consume a reply at most once. Conditional
per-document versions make a duplicate old `put` conflict after it has landed.
-/

namespace Resonate.Concrete

open Rover

abbrev Config := Experiment.Storage.Config
abbrev Version := Experiment.Storage.Version
abbrev OpId := Experiment.Storage.OpId
abbrev Key := Experiment.Ident

inductive Pid where
  | outside
  | server (address : Addr)
  | store
  deriving DecidableEq, Repr

inductive StoreRequest where
  | get (key : Key)
  | put (key : Key) (document : Promise)
      (expectedVersion : Option Version)
  deriving DecidableEq, Repr

inductive StoreReply where
  | got (document : Option (Promise × Version))
  | written
  | conflict
  /-- A failed write may have landed. -/
  | failed
  deriving DecidableEq, Repr

inductive Msg (_config : Resonate.Config) where
  | request (call : Call)
  | output (output : Output)
  | callGet (op : OpId) (key : Key)
  | callPut (op : OpId) (key : Key) (document : Promise)
      (expectedVersion : Option Version)
  | replyGot (op : OpId) (document : Option (Promise × Version))
  | replyWritten (op : OpId)
  | replyConflict (op : OpId)
  | replyFailed (op : OpId)
  deriving DecidableEq, Repr

/-- Build an RPC request envelope around an application-level payload. -/
@[simp] def Msg.call (op : OpId) : StoreRequest → Msg appConfig
  | .get key => .callGet op key
  | .put key document expectedVersion =>
      .callPut op key document expectedVersion

/-- Build an RPC reply envelope around an application-level payload. -/
@[simp] def Msg.reply (op : OpId) : StoreReply → Msg appConfig
  | .got document => .replyGot op document
  | .written => .replyWritten op
  | .conflict => .replyConflict op
  | .failed => .replyFailed op

inductive Phase where
  | loading
  | writing
  deriving DecidableEq, Repr

/-- Node-local provenance for one outstanding store operation.

None of `call`, `loaded`, or `selected` is copied into a `put`. -/
structure Flight where
  call : Call
  loaded : Option (Promise × Version) := none
  after : Option State := none
  document : Option Promise := none
  selected : List Output := []
  attempt : Nat := 0
  phase : Phase := .loading
  deriving DecidableEq, Repr

structure Node where
  nextOp : OpId := 0
  flights : List (OpId × Flight) := []
  /-- Append-only local provenance indexed by never-reused operation ids. -/
  history : List (OpId × Flight) := []
  deriving DecidableEq, Repr

abbrev Store := Experiment.Storage.Store

inductive Local where
  | outside
  | node (state : Node)
  | store (state : Store)

def Msg.call? {config : Resonate.Config} : Msg config → Option Resonate.Call
  | .request value => some value
  | .output _ => none
  | .callGet _ _ | .callPut _ _ _ _
  | .replyGot _ _ | .replyWritten _
  | .replyConflict _ | .replyFailed _ => none

def requestKey (call : Call) : Key := call.request.key

def documentState (document : Option (Promise × Version)) : State :=
  { promises := document.toList.map (·.1) }

def Store.document (store : Store) (key : Key) :
    Option (Promise × Version) :=
  store.docs.find? (·.1 == key) |>.map fun (_, document, version) =>
    (document, version)

def Store.version (store : Store) (key : Key) : Option Version :=
  (store.document key).map (·.2)

def Store.commit (store : Store) (key : Key) (document : Promise) : Store :=
  let version := (store.version key).getD 0 + 1
  { docs :=
      (key, document, version) :: store.docs.filter (·.1 != key) }

def Store.toState (store : Store) : State :=
  { promises := store.docs.map (·.2.1) }

def Node.takeFlight (node : Node) (op : OpId) : Option Flight × Node :=
  let flight := (node.flights.find? (·.1 == op)).map (·.2)
  (flight, { node with flights := node.flights.filter (·.1 != op) })

def Node.await (node : Node) (flight : Flight)
    (message : OpId → Msg appConfig) :
    Node × (Pid × Msg appConfig) :=
  let op := node.nextOp
  ({ nextOp := op + 1
     flights := (op, flight) :: node.flights
     history := (op, flight) :: node.history },
    (.store, message op))

def sendOutputs {appConfig : Resonate.Config} (outputs : List Output) :
    List (Pid × Msg appConfig) :=
  outputs.map fun output => (.outside, .output output)

def unavailable (call : Call) : Output :=
  .response call.client call.id { status := 503 }

/-- Evaluate the handler against the loaded one-document footprint.  The
membership witness remains a ghost fact about the selected branch; the wire
message produced below is a raw `put`. -/
def decideResults (appConfig : Resonate.Config) (node : Node)
    (flight : Flight) (document : Option (Promise × Version)) :
    Outcomes (Result Pid Local (Msg appConfig)) :=
  let before := documentState document
  let outcomes :=
    Resonate.dispatch { appConfig with unreliable := true }
      flight.call before
  ⟨outcomes.val.map fun (after, outputs) =>
      match after.promises.find? (·.id == requestKey flight.call) with
      | none =>
          { state := .node node, send := sendOutputs [unavailable flight.call] }
      | some nextDocument =>
          if after.promises == [nextDocument] then
            let writing : Flight := {
              flight with
              loaded := document
              after := some after
              document := some nextDocument
              selected := outputs
              phase := .writing
            }
            let (nextNode, message) :=
              node.await writing fun op =>
                .call op (.put (requestKey flight.call) nextDocument
                  (document.map (·.2)))
            { state := .node nextNode, send := [message] }
          else
            { state := .node node
              send := sendOutputs [unavailable flight.call] },
    by
      obtain ⟨head, tail, h⟩ :=
        List.exists_cons_of_ne_nil outcomes.property
      rw [h]
      simp⟩

def storePutResults (config : Config) (server : Addr) (store : Store)
    (op : OpId) (key : Key) (document : Promise)
    (expectedVersion : Option Version) :
    Outcomes (Result Pid Local (Msg appConfig)) :=
  if config.conditional && expectedVersion != store.version key then
    Outcomes.one {
      state := .store store
      send := [(.server server, .reply op .conflict)]
    }
  else
    let committed := store.commit key document
    if config.flaky then
      ⟨[
        { state := .store committed
          send := [(.server server, .reply op .written)] },
        { state := .store committed
          send := [(.server server, .reply op .failed)] },
        { state := .store store
          send := [(.server server, .reply op .failed)] }
      ], by simp⟩
    else
      Outcomes.one {
        state := .store committed
        send := [(.server server, .reply op .written)]
      }

def nodeGotResults (appConfig : Resonate.Config) (node : Node)
    (op : OpId) (document : Option (Promise × Version)) :
    Outcomes (Result Pid Local (Msg appConfig)) :=
  let (flight, nextNode) := node.takeFlight op
  match flight with
  | some flight =>
      match flight.phase with
      | .loading =>
          if document.all fun value =>
              value.1.id == requestKey flight.call then
            decideResults appConfig nextNode flight document
          else
            Outcomes.one {
              state := .node nextNode
              send := sendOutputs [unavailable flight.call]
            }
      | .writing => Outcomes.one { state := .node nextNode, send := [] }
  | none => Outcomes.one { state := .node node, send := [] }

def step (appConfig : Resonate.Config) (config : Config) (pid : Pid)
    (localState : Local) (_now : Time) (event : Event Pid (Msg appConfig)) :
    Outcomes (Result Pid Local (Msg appConfig)) :=
  match pid, localState, event with
  | .server _, .node node, .receive .outside (.request call) =>
      let loading : Flight := { call }
      let (nextNode, message) :=
        node.await loading fun op => .call op (.get (requestKey call))
      Outcomes.one {
        state := .node nextNode
        send := [message]
      }
  | .server _, .node node, .receive .store (.replyGot op document) =>
      nodeGotResults appConfig node op document
  | .server _, .node node, .receive .store (.replyWritten op) =>
      let (flight, nextNode) := node.takeFlight op
      match flight with
      | some flight =>
          match flight.phase with
          | .writing =>
              Outcomes.one {
                state := .node nextNode
                send := sendOutputs flight.selected
              }
          | .loading => Outcomes.one { state := .node nextNode, send := [] }
      | none => Outcomes.one { state := .node node, send := [] }
  | .server _, .node node, .receive .store (.replyConflict op) =>
      let (flight, nextNode) := node.takeFlight op
      match flight with
      | some flight =>
          match flight.phase with
          | .writing =>
              if flight.attempt < config.retries then
                let loading : Flight := {
                  flight with
                  loaded := none
                  after := none
                  document := none
                  selected := []
                  attempt := flight.attempt + 1
                  phase := .loading
                }
                let (retryNode, message) :=
                  nextNode.await loading fun nextOp =>
                    .call nextOp (.get (requestKey flight.call))
                Outcomes.one {
                  state := .node retryNode
                  send := [message]
                }
              else
                Outcomes.one {
                  state := .node nextNode
                  send := sendOutputs [unavailable flight.call]
                }
          | .loading => Outcomes.one { state := .node nextNode, send := [] }
      | none => Outcomes.one { state := .node node, send := [] }
  | .server _, .node node, .receive .store (.replyFailed op) =>
      let (flight, nextNode) := node.takeFlight op
      match flight with
      | some flight =>
          Outcomes.one {
            state := .node nextNode
            send := sendOutputs [unavailable flight.call]
          }
      | none => Outcomes.one { state := .node node, send := [] }
  | .store, .store store, .receive (.server server) (.callGet op key) =>
      Outcomes.one {
        state := .store store
        send := [(.server server, .replyGot op (store.document key))]
      }
  | .store, .store store,
      .receive (.server server)
        (.callPut op key document expectedVersion) =>
      storePutResults config server store op key document expectedVersion
  | _, _, _ => Outcomes.one { state := localState, send := [] }

abbrev model (nodes : List Addr) (appConfig : Resonate.Config) : Model where
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
    process .store = .store {} ∧
    ∀ address ∈ nodes, process (.server address) = .node {}
  step := step appConfig

def initialProcess : Pid → Local
  | .outside => .outside
  | .server _ => .node {}
  | .store => .store {}

theorem initialProcess_valid (nodes : List Addr) (appConfig : Resonate.Config)
    (config : Config) (hnodup : nodes.Nodup) :
    (model nodes appConfig).init config initialProcess := by
  refine ⟨hnodup, rfl, ?_⟩
  intros
  rfl

def boundaryEvent (nodes : List Addr) (appConfig : Resonate.Config) :
    Rover.BoundaryEvent (model nodes appConfig) → Option Resonate.BoundaryEvent
  | .input _ time (.request call) => some (.request time call)
  | .output _ time (.output (.response client id response)) =>
      some (.response time client id response)
  | .output _ time (.output (.notification client record)) =>
      some (.notification time client record)
  | _ => none

def boundaryTrace (nodes : List Addr) (appConfig : Resonate.Config)
    (execution : Execution (model nodes appConfig)) :
    List Resonate.BoundaryEvent :=
  (Rover.trace execution).filterMap (boundaryEvent nodes appConfig)

def ValidBoundaryTrace (nodes : List Addr) (appConfig : Resonate.Config)
    (config : Config) (events : List Resonate.BoundaryEvent) : Prop :=
  ∃ execution,
    Behavior (model nodes appConfig) config execution ∧
    boundaryTrace nodes appConfig execution = events

end Resonate.Concrete

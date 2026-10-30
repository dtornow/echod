import Resonate.Abstract

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

abbrev Version := Nat
abbrev OpId := Nat

structure Config where
  conditional : Bool := true
  flaky : Bool := false
  retries : Nat := 3
  /-- The one process that advances timeout workflows. External traffic may
  still use every node in the duplicate-free deployment. -/
  workflowNode : Addr := ""

inductive Pid where
  | outside
  | node (address : Addr)
  | store
  deriving DecidableEq, Repr

/-- Application payload of a store request. Correlation is deliberately not
part of this type. -/
inductive StoreRequest where
  | get (key : DocumentKey)
  | put (key : DocumentKey) (document : Document key)
      (expectedVersion : Option Version)

/-- Application payload of a store reply. The key on `got` is the dependent
index needed to type the returned document; correlation remains external. -/
inductive StoreReply where
  | got (key : DocumentKey)
      (document : Option (Document key × Version))
  | written
  | conflict
  /-- The write may have landed. -/
  | failed

structure RpcRequest where
  op : OpId
  payload : StoreRequest

structure RpcReply where
  op : OpId
  payload : StoreReply

inductive Msg where
  | request (call : Call)
  | output (output : Output)
  | storeRequest (rpc : RpcRequest)
  | storeReply (rpc : RpcReply)

structure Versioned (key : DocumentKey) where
  document : Document key
  version : Version

/-- The physical store has one optional, independently versioned value for
each dependent document key. `keys` is only the finite discovery index. -/
structure Store where
  keys : List DocumentKey := []
  values : (key : DocumentKey) → Option (Versioned key) := fun _ => none

def Store.read (store : Store) (key : DocumentKey) :
    Option (Document key × Version) :=
  (store.values key).map fun value => (value.document, value.version)

def Store.version (store : Store) (key : DocumentKey) : Option Version :=
  (store.values key).map (·.version)

theorem Store.version_eq_read (store : Store) (key : DocumentKey) :
    store.version key = (store.read key).map (·.2) := by
  unfold Store.version Store.read
  cases store.values key <;> rfl

def Store.commit (store : Store) (key : DocumentKey)
    (document : Document key) : Store :=
  let version := (store.version key).getD 0 + 1
  { keys :=
      if store.keys.contains key then store.keys else store.keys ++ [key]
    values := fun other =>
      if h : other = key then
        some {
          document := h ▸ document
          version
        }
      else
        store.values other }

@[simp] theorem Store.read_commit_same (store : Store) (key : DocumentKey)
    (document : Document key) :
    (store.commit key document).read key =
      some (document, (store.version key).getD 0 + 1) := by
  simp [Store.commit, Store.read]

@[simp] theorem Store.read_commit_other (store : Store)
    (key other : DocumentKey) (document : Document key)
    (h : other ≠ key) :
    (store.commit key document).read other = store.read other := by
  simp [Store.commit, Store.read, h]

def Store.toAbstract (store : Store) : Resonate.Store where
  keys := store.keys
  documents := fun key =>
    match store.values key with
    | some value => value.document
    | none => emptyDocument key

@[simp] theorem Store.toAbstract_commit (store : Store)
    (key : DocumentKey) (document : Document key) :
    (store.commit key document).toAbstract =
      store.toAbstract.write key document := by
  unfold Store.commit Store.toAbstract Resonate.Store.write
  congr 1
  funext other
  by_cases h : other = key
  · subst other
    simp
  · simp [h]

/-- Consume a successful conditional attempt without installing its candidate
payload. This is the not-landed failure fence: the logical document is
unchanged, but replaying the same expected version can no longer land later
after its node-local continuation has been discarded. -/
def Store.fence (store : Store) (key : DocumentKey) : Store :=
  store.commit key (store.toAbstract.read key)

@[simp] theorem Store.toAbstract_read_fence (store : Store)
    (key other : DocumentKey) :
    (store.fence key).toAbstract.read other =
      store.toAbstract.read other := by
  rw [Store.fence, Store.toAbstract_commit]
  by_cases h : other = key
  · subst other
    simp
  · simp [h]

inductive PendingEntry where
  | occurrence (request : ServerModel.PromiseCreateReq) (instant : Time)
  deriving Repr

def PendingEntry.key : PendingEntry → DocumentKey
  | .occurrence request _ => .origin request.id.origin

def PendingEntry.toWorkflow? : PendingEntry → Option Resonate.WorkflowEntry
  | .occurrence request instant => some { request, instant }

def PendingEntry.fromWorkflow (entry : Resonate.WorkflowEntry) : PendingEntry :=
  .occurrence entry.request entry.instant

def pendingWorkflow (entries : List PendingEntry) :
    List Resonate.WorkflowEntry :=
  entries.filterMap PendingEntry.toWorkflow?

@[simp] theorem pendingWorkflow_map_fromWorkflow
    (entries : List Resonate.WorkflowEntry) :
    pendingWorkflow (entries.map PendingEntry.fromWorkflow) = entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      simp [pendingWorkflow, PendingEntry.fromWorkflow,
        PendingEntry.toWorkflow?, Function.comp_apply] at ih ⊢
      exact ih

inductive Transaction where
  | external (call : Call)
  | work (item : WorkItem) (now : Time) (rest : List PendingEntry)
  | scan (key : DocumentKey) (now : Time) (rest : List PendingEntry)

def Transaction.key? : Transaction → Option DocumentKey
  | .external call =>
      match call.request with
      | .promiseGet req => some (.origin req.id.origin)
      | .promiseCreate req => some (.origin req.id.origin)
      | .promiseSettle req => some (.origin req.id.origin)
      | .promiseRegisterCallback req =>
          if req.awaited.sameOrigin req.awaiter then
            some (.origin req.awaited.origin)
          else none
      | .promiseRegisterListener req => some (.origin req.awaited.origin)
      | .promiseSearch _ => none
      | .scheduleGet req => some (.schedule req.id)
      | .scheduleCreate req => some (.schedule req.id)
      | .scheduleDelete req => some (.schedule req.id)
      | .scheduleSearch _ => none
      | .taskGet req => some (.origin req.id.origin)
      | .taskCreate req => some (.origin req.action.id.origin)
      | .taskAcquire req => some (.origin req.id.origin)
      | .taskFence req =>
          if req.action.targetId != req.id ∧
              req.action.targetId.sameOrigin req.id then
            some (.origin req.id.origin)
          else none
      | .taskHeartbeat req =>
          match req.tasks with
          | [] => none
          | first :: _ =>
              if sameOriginRefs first.id.origin req.tasks then
                some (.origin first.id.origin)
              else none
      | .taskSuspend req =>
          if req.actions.any (fun action =>
              !action.awaited.sameOrigin req.id) then
            none
          else some (.origin req.id.origin)
      | .taskFulfill req =>
          if req.action.id.sameOrigin req.id then
            some (.origin req.id.origin)
          else none
      | .taskRelease req => some (.origin req.id.origin)
      | .taskHalt req => some (.origin req.id.origin)
      | .taskContinue req => some (.origin req.id.origin)
      | .taskSearch _ => none
  | .work item _ _ => some item.key
  | .scan key _ _ => some key

inductive Phase where
  | loading
  | writing
  deriving DecidableEq, Repr

/-- A node-local continuation. `loaded`, `document`, selected boundary
outputs, and schedule occurrence continuations never enter a store payload. -/
structure Flight where
  key : DocumentKey
  transaction : Transaction
  loaded : Option (Document key × Version) := none
  document : Option (Document key) := none
  selected : List Output := []
  continuations : List PendingEntry := []
  attempt : Nat := 0
  phase : Phase := .loading

structure Node where
  nextOp : OpId := 0
  flights : List (OpId × Flight) := []
  /-- Keys whose document transaction received a definite written reply. -/
  known : List DocumentKey := []
  /-- Process-local schedule occurrence and timeout workflow. -/
  pending : List PendingEntry := []
  /-- An ambiguous internal PUT failure permanently stops this local workflow.
  External requests remain available. This prevents guessing whether a
  schedule/occurrence write landed. -/
  workflowBlocked : Bool := false

inductive Local where
  | outside
  | node (state : Node)
  | store (state : Store)

def Node.remember (node : Node) (key : DocumentKey) : Node :=
  if node.known.contains key then node
  else { node with known := node.known ++ [key] }

def Node.takeFlight (node : Node) (op : OpId) : Option Flight × Node :=
  let flight := (node.flights.find? (·.1 == op)).map (·.2)
  (flight, { node with flights := node.flights.filter (·.1 != op) })

def Node.await (node : Node) (flight : Flight)
    (payload : StoreRequest) : Node × (Pid × Msg) :=
  let op := node.nextOp
  ({ node with
      nextOp := op + 1
      flights := (op, flight) :: node.flights },
    (.store, .storeRequest { op, payload }))

def sendOutputs (outputs : List Output) : List (Pid × Msg) :=
  outputs.map fun output => (.outside, .output output)

/-- The protocol has operation-specific response types, so a transport
failure uses the existing unreliable abstract transition rather than
fabricating a response of the wrong constructor. Until that transition is
selected, failed internal work is silent. -/
def failureOutputs : Transaction → List Output
  | .external call => [Resonate.unavailable call]
  | .work _ _ _ | .scan _ _ _ => []

def singleState (key : DocumentKey) (document : Document key) : State :=
  { store := ({} : Resonate.Store).write key document }

def selectedExternal (appConfig : Resonate.Config) (call : Call)
    (key : DocumentKey) (document : Document key) :
    State × List Output :=
  Resonate.run { appConfig with unreliable := true } call
    (singleState key document)

def selectedWork (appConfig : Resonate.Config) (item : WorkItem)
    (now : Time) (rest : List PendingEntry)
    (key : DocumentKey) (document : Document key) :
    State × List Output :=
  Resonate.runWork { appConfig with unreliable := true } item now
    (pendingWorkflow rest)
    (singleState key document)

def Transaction.isExternal : Transaction → Bool
  | .external _ => true
  | .work _ _ _ | .scan _ _ _ => false

structure Candidate (key : DocumentKey) where
  document : Document key
  outputs : List Output
  continuations : List PendingEntry

def selectScan (appConfig : Resonate.Config) (key : DocumentKey)
    (now : Time) (rest : List PendingEntry) (document : Document key) :
    Option (Candidate key) :=
  match key with
  | .origin origin =>
      match (Direct.originWork origin document now).head? with
      | none => none
      | some item =>
          let result := selectedWork appConfig item now rest
            (.origin origin) document
          some {
            document := result.1.store.read (.origin origin)
            outputs := result.2
            continuations :=
              result.1.workflow.pending.map PendingEntry.fromWorkflow
          }
  | .schedule id =>
      match document with
      | some schedule =>
          if schedule.nextRunAt ≤ now then
            let result := selectedWork appConfig (.scheduleTimeout id)
              now rest (.schedule id) document
            some {
              document := result.1.store.read (.schedule id)
              outputs := result.2
              continuations :=
                result.1.workflow.pending.map PendingEntry.fromWorkflow
            }
          else none
      | none => none

theorem selectScan_origin_some
    (appConfig : Resonate.Config) (origin : String) (now : Time)
    (rest : List PendingEntry) (document : OriginDocument origin)
    (candidate : Candidate (.origin origin))
    (hselect :
      selectScan appConfig (.origin origin) now rest document =
        some candidate) :
    ∃ item,
      item ∈ Direct.originWork origin document now ∧
      let result := selectedWork appConfig item now rest
        (.origin origin) document
      candidate.document = result.1.store.read (.origin origin) ∧
      candidate.outputs = result.2 ∧
      candidate.continuations =
        result.1.workflow.pending.map PendingEntry.fromWorkflow := by
  cases hhead : (Direct.originWork origin document now).head? with
  | none =>
      simp only [selectScan] at hselect
      rw [hhead] at hselect
      contradiction
  | some item =>
      simp only [selectScan] at hselect
      rw [hhead] at hselect
      have hcandidate : candidate = {
          document :=
            (selectedWork appConfig item now rest
              (.origin origin) document).1.store.read (.origin origin)
          outputs :=
            (selectedWork appConfig item now rest
              (.origin origin) document).2
          continuations :=
            (selectedWork appConfig item now rest
              (.origin origin) document).1.workflow.pending.map
                PendingEntry.fromWorkflow
        } := by
        exact (Option.some.inj hselect).symm
      subst candidate
      refine ⟨item, ?_, rfl, rfl, rfl⟩
      obtain ⟨remaining, hitems⟩ := List.head?_eq_some_iff.mp hhead
      rw [hitems]
      exact List.mem_cons_self

theorem selectScan_schedule_some
    (appConfig : Resonate.Config) (id : ServerModel.Ident) (now : Time)
    (rest : List PendingEntry) (document : ScheduleDocument id)
    (candidate : Candidate (.schedule id))
    (hselect :
      selectScan appConfig (.schedule id) now rest document =
        some candidate) :
    ∃ schedule,
      document = some schedule ∧ schedule.nextRunAt ≤ now ∧
      let result := selectedWork appConfig (.scheduleTimeout id) now rest
        (.schedule id) document
      candidate.document = result.1.store.read (.schedule id) ∧
      candidate.outputs = result.2 ∧
      candidate.continuations =
        result.1.workflow.pending.map PendingEntry.fromWorkflow := by
  cases hdocument : document with
  | none =>
      simp only [selectScan] at hselect
      rw [hdocument] at hselect
      contradiction
  | some schedule =>
      subst document
      simp only [selectScan] at hselect
      by_cases hdue : schedule.nextRunAt ≤ now
      · simp only [if_pos hdue] at hselect
        have hcandidate : candidate = {
            document :=
              (selectedWork appConfig (.scheduleTimeout id) now rest
                (.schedule id) (some schedule)).1.store.read (.schedule id)
            outputs :=
              (selectedWork appConfig (.scheduleTimeout id) now rest
                (.schedule id) (some schedule)).2
            continuations :=
              (selectedWork appConfig (.scheduleTimeout id) now rest
                (.schedule id) (some schedule)).1.workflow.pending.map
                  PendingEntry.fromWorkflow
          } := by
          exact (Option.some.inj hselect).symm
        subst candidate
        exact ⟨schedule, rfl, hdue, rfl, rfl, rfl⟩
      · simp only [if_neg hdue] at hselect
        contradiction

def select (appConfig : Resonate.Config) (flight : Flight)
    (loaded : Option (Document flight.key × Version)) :
    Option (Candidate flight.key) :=
  let document := loaded.map (·.1) |>.getD (emptyDocument flight.key)
  match flight.transaction with
  | .external call =>
      let result := selectedExternal appConfig call flight.key document
      some {
        document := result.1.store.read flight.key
        outputs := result.2
        continuations :=
          result.1.workflow.pending.map PendingEntry.fromWorkflow
      }
  | .work item now rest =>
      if item.key = flight.key then
        let result :=
          selectedWork appConfig item now rest flight.key document
        some {
          document := result.1.store.read flight.key
          outputs := result.2
          continuations :=
            result.1.workflow.pending.map PendingEntry.fromWorkflow
        }
      else none
  | .scan key now rest =>
      if h : key = flight.key then
        h ▸ selectScan appConfig key now rest (h.symm ▸ document)
      else none

def decide (appConfig : Resonate.Config) (node : Node) (flight : Flight)
    (loaded : Option (Document flight.key × Version)) :
    Result Pid Local Msg :=
  match select appConfig flight loaded with
  | none => { state := .node node, send := [] }
  | some candidate =>
      let writing : Flight := {
        flight with
        loaded
        document := some candidate.document
        selected := candidate.outputs
        continuations := candidate.continuations
        phase := .writing
      }
      let (nextNode, request) :=
        node.await writing
          (.put flight.key candidate.document (loaded.map (·.2)))
      { state := .node nextNode, send := [request] }

def retry (config : Config) (node : Node) (flight : Flight) :
    Result Pid Local Msg :=
  if flight.attempt < config.retries then
    let loading : Flight := {
      flight with
      loaded := none
      document := none
      selected := []
      continuations := []
      attempt := flight.attempt + 1
      phase := .loading
    }
    let (next, request) :=
      node.await loading (.get flight.key)
    { state := .node next, send := [request] }
  else
    { state := .node node, send := sendOutputs (failureOutputs flight.transaction) }

def storePut (config : Config) (sender : Pid) (store : Store)
    (op : OpId) (key : DocumentKey) (document : Document key)
    (expectedVersion : Option Version) :
    Outcomes (Result Pid Local Msg) :=
  if config.conditional && expectedVersion != store.version key then
    Outcomes.one {
      state := .store store
      send := [(sender, .storeReply { op, payload := .conflict })]
    }
  else
    let committed := store.commit key document
    if config.flaky then
      ⟨[
        { state := .store committed
          send := [(sender, .storeReply { op, payload := .written })] },
        { state := .store committed
          send := [(sender, .storeReply { op, payload := .failed })] },
        { state := .store (store.fence key)
          send := [(sender, .storeReply { op, payload := .failed })] }
      ], by simp⟩
    else
      Outcomes.one {
        state := .store committed
        send := [(sender, .storeReply { op, payload := .written })]
      }

def start (node : Node) (transaction : Transaction)
    (key : DocumentKey) : Result Pid Local Msg :=
  let flight : Flight := { key, transaction }
  let (next, request) := node.await flight (.get key)
  { state := .node next, send := [request] }

def pureExternal (appConfig : Resonate.Config) (node : Node) (call : Call) :
    Result Pid Local Msg :=
  let result := Resonate.run { appConfig with unreliable := true } call {}
  { state := .node node, send := sendOutputs result.2 }

def step (appConfig : Resonate.Config) (config : Config) (pid : Pid)
    (localState : Local) (now : Time) (event : Event Pid Msg) :
    Outcomes (Result Pid Local Msg) :=
  match pid, localState, event with
  | .node address, .node node, .receive .outside (.request call) =>
      if address != config.workflowNode || !node.flights.isEmpty then
        Outcomes.one { state := .node node, send := [] }
      else
        match (Transaction.external call).key? with
        | some key => Outcomes.one (start node (.external call) key)
        | none => Outcomes.one (pureExternal appConfig node call)
  | .node address, .node node, .timeout =>
      if address != config.workflowNode || node.workflowBlocked ||
          !node.flights.isEmpty then
        Outcomes.one { state := .node node, send := [] }
      else
        match node.pending with
        | entry :: rest =>
            let transaction :=
              match entry with
              | .occurrence request instant =>
                  Transaction.work (.occurrence request instant) instant rest
            Outcomes.one (start { node with pending := [] }
              transaction entry.key)
        | [] =>
            match node.known.head? with
            | some key =>
                Outcomes.one (start node (.scan key now []) key)
            | none => Outcomes.one { state := .node node, send := [] }
  | .node _, .node node,
      .receive .store (.storeReply { op, payload := .got key loaded }) =>
      let (flight, next) := node.takeFlight op
      match flight with
      | some flight =>
          if h : key = flight.key then
            match flight.phase with
            | .loading =>
                Outcomes.one (decide appConfig next flight (h ▸ loaded))
            | .writing =>
                Outcomes.one { state := .node next, send := [] }
          else
            Outcomes.one { state := .node next, send := [] }
      | none => Outcomes.one { state := .node node, send := [] }
  | .node _, .node node,
      .receive .store (.storeReply { op, payload := .written }) =>
      let (flight, next) := node.takeFlight op
      match flight with
      | some flight =>
          match flight.phase with
          | .writing =>
              Outcomes.one {
                state := .node {
                  next.remember flight.key with
                    pending := flight.continuations ++ next.pending }
                send := sendOutputs flight.selected
              }
          | .loading => Outcomes.one { state := .node next, send := [] }
      | none => Outcomes.one { state := .node node, send := [] }
  | .node _, .node node,
      .receive .store (.storeReply { op, payload := .conflict }) =>
      let (flight, next) := node.takeFlight op
      match flight with
      | some flight =>
          match flight.phase with
          | .writing =>
              if flight.transaction.isExternal then
                Outcomes.one (retry config next flight)
              else
                Outcomes.one {
                  state := .node { next with workflowBlocked := true }
                  send := []
                }
          | .loading => Outcomes.one { state := .node next, send := [] }
      | none => Outcomes.one { state := .node node, send := [] }
  | .node _, .node node,
      .receive .store (.storeReply { op, payload := .failed }) =>
      let (flight, next) := node.takeFlight op
      match flight with
      | some flight =>
          Outcomes.one {
            state := .node {
              next with workflowBlocked :=
                next.workflowBlocked || !flight.transaction.isExternal }
            send := sendOutputs (failureOutputs flight.transaction)
          }
      | none => Outcomes.one { state := .node node, send := [] }
  | .store, .store store,
      .receive sender (.storeRequest { op, payload := .get key }) =>
      Outcomes.one {
        state := .store store
        send := [(sender, .storeReply {
          op, payload := .got key (store.read key) })]
      }
  | .store, .store store,
      .receive sender
        (.storeRequest { op, payload := .put key document expected }) =>
      storePut config sender store op key document expected
  | _, _, _ => Outcomes.one { state := localState, send := [] }

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
  outside_not_process := by simp
  injectable := fun _ message => ∃ call, message = .request call
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

def boundaryTrace (execution : Execution (model nodes appConfig)) :
    List Resonate.BoundaryEvent :=
  (Rover.trace execution).filterMap boundaryEvent

def ValidBoundaryTrace (nodes : List Addr) (appConfig : Resonate.Config)
    (config : Config) (events : List Resonate.BoundaryEvent) : Prop :=
  ∃ execution,
    Behavior (model nodes appConfig) config execution ∧
    boundaryTrace execution = events

end Resonate.Concrete

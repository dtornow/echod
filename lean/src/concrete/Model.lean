import Rover
import «concrete».Timers
import «concrete».Internal

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
  flaky : Bool := false
  retries : Nat := 3
  bucketWidth : Time := 1000
  loadAhead : Time := 2000
  heartbeat : Time := 1000
  nodeTtl : Time := 5000
  fireConcurrency : Nat := 16

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
  | armTimer (key : TimerKey)
  | deleteTimer (key : TimerKey)
  | deleteTimers (keys : List TimerKey)
  | listTimers (through : Time)
  | announce (announcement : Announcement)
  | listAnnouncements
  | getMembership
  | putMembership (expectedVersion : Version) (next : MembershipConfig)

/-- Application payload of a store reply. The key on `got` is the dependent
index needed to type the returned document; correlation remains external. -/
inductive StoreReply where
  | got (key : DocumentKey)
      (document : Option (Document key × Version))
  | written
  | conflict
  /-- The write may have landed. -/
  | failed
  | done
  | timers (keys : List TimerKey)
  | announcements (values : List Announcement)
  | membership (configuration : MembershipConfig) (version : Version)

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

/-- A dependent cache entry: the value's type is fixed by its key. -/
structure CacheEntry where
  key : DocumentKey
  value : Versioned key

inductive Control where
  | announced (now : Time)
  | announcements (now : Time)
  | membership (now : Time) (live : List Addr)
  | membershipWrite (now : Time)
  | timerList (now through : Time) (kind : ListingKind)
  | cleanup (outputs : List Output)
  deriving Repr

/-- The physical store has one optional, independently versioned value for
each dependent document key. `keys` is only the finite discovery index. -/
structure Store where
  keys : List DocumentKey := []
  values : (key : DocumentKey) → Option (Versioned key) := fun _ => none
  timers : TimerObjects := {}
  membership : MembershipObjects := {}

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
  { store with
    keys :=
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

@[simp] theorem map_fromWorkflow_pendingWorkflow
    (entries : List PendingEntry) :
    (pendingWorkflow entries).map PendingEntry.fromWorkflow = entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨request, instant⟩ := entry
      simp only [pendingWorkflow, PendingEntry.toWorkflow?,
        PendingEntry.fromWorkflow, List.filterMap_cons,
        Option.toList_some, List.map_cons] at ih ⊢
      exact congrArg
        (fun tail => PendingEntry.occurrence request instant :: tail) ih

inductive Transaction where
  | external (call : Call)
  | work (item : WorkItem) (now : Time) (rest : List PendingEntry)
  | sweep (timer : TimerKey) (now : Time) (rest : List PendingEntry)

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
  | .sweep timer _ _ => some timer.target.key

inductive Phase where
  | loading
  | arming
  | writing
  | deleting
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
  address : Addr := ""
  armed : Option TimerKey := none
  fired : Option TimerKey := none
  cleanup : List TimerKey := []

structure Node where
  nextOp : OpId := 0
  nextTimerToken : TimerToken := 0
  flights : List (OpId × Flight) := []
  controls : List (OpId × Control) := []
  /-- A non-authoritative node-local read cache. Every decision is still
  validated by a raw conditional PUT. -/
  cache : List CacheEntry := []
  /-- Process-local schedule occurrence and timeout workflow. -/
  pending : List PendingEntry := []
  membership : MembershipView := {}
  wheel : TimerWheel := {}
  armed : List ArmedEntry := []
  nextHeartbeat : Option Time := some 0

inductive Local where
  | outside
  | node (state : Node)
  | store (state : Store)

def CacheEntry.read (entry : CacheEntry) (key : DocumentKey) :
    Option (Versioned key) :=
  if h : entry.key = key then some (h ▸ entry.value) else none

def Node.cacheRead (node : Node) (key : DocumentKey) : Option (Versioned key) :=
  node.cache.findSome? (·.read key)

def Node.cachePut (node : Node) (key : DocumentKey)
    (value : Versioned key) : Node :=
  { node with
    cache := { key, value } :: node.cache.filter (·.key != key) }

def Node.cacheInvalidate (node : Node) (key : DocumentKey) : Node :=
  { node with cache := node.cache.filter (·.key != key) }

def Node.previousArmed? (node : Node) (flight : Flight) : Option TimerKey :=
  match flight.loaded.map (·.2) with
  | none => none
  | some version =>
      (node.armed.find? fun entry =>
        entry.target == flight.key && entry.version == version).map (·.timer)

def Node.noteArmed (node : Node) (flight : Flight) : Node :=
  let retained := node.armed.filter (·.target != flight.key)
  match flight.armed with
  | none => { node with armed := retained }
  | some timer =>
      { node with
        armed := {
          target := flight.key
          timer
          version :=
            (flight.loaded.map fun loaded => loaded.2).getD 0 + 1
        } :: retained }

def Node.takeFlight (node : Node) (op : OpId) : Option Flight × Node :=
  let flight := (node.flights.find? (·.1 == op)).map (·.2)
  (flight, { node with flights := node.flights.filter (·.1 != op) })

def Node.takeControl (node : Node) (op : OpId) : Option Control × Node :=
  let control := (node.controls.find? (·.1 == op)).map (·.2)
  (control, { node with controls := node.controls.filter (·.1 != op) })

def Node.await (node : Node) (flight : Flight)
    (payload : StoreRequest) : Node × (Pid × Msg) :=
  let op := node.nextOp
  ({ node with
      nextOp := op + 1
      flights := (op, flight) :: node.flights },
    (.store, .storeRequest { op, payload }))

def Node.awaitControl (node : Node) (control : Control)
    (payload : StoreRequest) : Node × (Pid × Msg) :=
  let op := node.nextOp
  ({ node with
      nextOp := op + 1
      controls := (op, control) :: node.controls },
    (.store, .storeRequest { op, payload }))

def sendOutputs (outputs : List Output) : List (Pid × Msg) :=
  outputs.map fun output => (.outside, .output output)

/-- A concrete document decision and its node-local effects. -/
structure Candidate (key : DocumentKey) where
  document : Document key
  outputs : List Output
  continuations : List PendingEntry

/-- The protocol has operation-specific response types, so a transport
failure uses the existing unreliable abstract transition rather than
fabricating a response of the wrong constructor. Until that transition is
selected, failed internal work is silent. -/
def failureOutputs : Transaction → List Output
  | .external call => [Resonate.unavailable call]
  | .work _ _ _ | .sweep _ _ _ => []

def Transaction.isExternal : Transaction → Bool
  | .external _ => true
  | .work _ _ _ | .sweep _ _ _ => false

def Transaction.logicalTime : Transaction → Time
  | .external call => call.requestedAt
  | .work _ now _ => now
  | .sweep _ now _ => now

def Candidate.cast {left right : DocumentKey} (h : left = right)
    (candidate : Candidate left) : Candidate right :=
  h ▸ candidate

def externalCandidate {key : DocumentKey} (appConfig : Resonate.Config)
    (call : Call) (document : Document key)
    (action : Decision.Handler key α) (wrap : α → Response) :
    Candidate key :=
  let (response, next, emitted) :=
    Decision.run appConfig.toServerConfig action document
  { document := next
    outputs := .response call.client call.id (wrap response) ::
      emitted.map .message
    continuations := [] }

def selectedExternalCandidate (appConfig : Resonate.Config) (call : Call)
    (key : DocumentKey) (document : Document key) :
    Option (Candidate key) :=
  match call.request with
  | .promiseGet req =>
      if h : DocumentKey.origin req.id.origin = key then
        some ((externalCandidate appConfig call (h ▸ document)
          (Decision.promiseGet req call.requestedAt) .promiseGet).cast h)
      else none
  | .promiseCreate req =>
      if h : DocumentKey.origin req.id.origin = key then
        some ((externalCandidate appConfig call (h ▸ document)
          (Decision.promiseCreate req call.requestedAt) .promiseCreate).cast h)
      else none
  | .promiseSettle req =>
      if h : DocumentKey.origin req.id.origin = key then
        some ((externalCandidate appConfig call (h ▸ document)
          (Decision.promiseSettle req call.requestedAt) .promiseSettle).cast h)
      else none
  | .promiseRegisterCallback req =>
      if h : DocumentKey.origin req.awaited.origin = key then
        some ((externalCandidate appConfig call (h ▸ document)
          (Decision.promiseRegisterCallback req call.requestedAt)
          .promiseRegisterCallback).cast h)
      else none
  | .promiseRegisterListener req =>
      if h : DocumentKey.origin req.awaited.origin = key then
        some ((externalCandidate appConfig call (h ▸ document)
          (Decision.promiseRegisterListener req call.requestedAt)
          .promiseRegisterListener).cast h)
      else none
  | .scheduleGet req =>
      if h : DocumentKey.schedule req.id = key then
        some ((externalCandidate appConfig call (h ▸ document)
          (Decision.scheduleGet req call.requestedAt) .scheduleGet).cast h)
      else none
  | .scheduleCreate req =>
      if h : DocumentKey.schedule req.id = key then
        some ((externalCandidate appConfig call (h ▸ document)
          (Decision.scheduleCreate req call.requestedAt) .scheduleCreate).cast h)
      else none
  | .scheduleDelete req =>
      if h : DocumentKey.schedule req.id = key then
        some ((externalCandidate appConfig call (h ▸ document)
          (Decision.scheduleDelete req call.requestedAt) .scheduleDelete).cast h)
      else none
  | .taskGet req =>
      if h : DocumentKey.origin req.id.origin = key then
        some ((externalCandidate appConfig call (h ▸ document)
          (Decision.taskGet req call.requestedAt) .taskGet).cast h)
      else none
  | .taskCreate req =>
      if h : DocumentKey.origin req.action.id.origin = key then
        some ((externalCandidate appConfig call (h ▸ document)
          (Decision.taskCreate req call.requestedAt) .taskCreate).cast h)
      else none
  | .taskAcquire req =>
      if h : DocumentKey.origin req.id.origin = key then
        some ((externalCandidate appConfig call (h ▸ document)
          (Decision.taskAcquire req call.requestedAt) .taskAcquire).cast h)
      else none
  | .taskFence req =>
      if h : DocumentKey.origin req.id.origin = key then
        some ((externalCandidate appConfig call (h ▸ document)
          (Decision.taskFence req call.requestedAt) .taskFence).cast h)
      else none
  | .taskHeartbeat req =>
      match req.tasks with
      | [] => none
      | first :: _ =>
          if h : DocumentKey.origin first.id.origin = key then
            some ((externalCandidate appConfig call (h ▸ document)
              (Decision.taskHeartbeat first.id.origin req call.requestedAt)
              .taskHeartbeat).cast h)
          else none
  | .taskSuspend req =>
      if h : DocumentKey.origin req.id.origin = key then
        some ((externalCandidate appConfig call (h ▸ document)
          (Decision.taskSuspend req call.requestedAt) .taskSuspend).cast h)
      else none
  | .taskFulfill req =>
      if h : DocumentKey.origin req.id.origin = key then
        some ((externalCandidate appConfig call (h ▸ document)
          (Decision.taskFulfill req call.requestedAt) .taskFulfill).cast h)
      else none
  | .taskRelease req =>
      if h : DocumentKey.origin req.id.origin = key then
        some ((externalCandidate appConfig call (h ▸ document)
          (Decision.taskRelease req call.requestedAt) .taskRelease).cast h)
      else none
  | .taskHalt req =>
      if h : DocumentKey.origin req.id.origin = key then
        some ((externalCandidate appConfig call (h ▸ document)
          (Decision.taskHalt req call.requestedAt) .taskHalt).cast h)
      else none
  | .taskContinue req =>
      if h : DocumentKey.origin req.id.origin = key then
        some ((externalCandidate appConfig call (h ▸ document)
          (Decision.taskContinue req call.requestedAt) .taskContinue).cast h)
      else none
  | .promiseSearch _ | .scheduleSearch _ | .taskSearch _ => none

def workCandidate {key : DocumentKey} (appConfig : Resonate.Config)
    (document : Document key) (action : Decision.Handler key α)
    (continuations : List PendingEntry) : Candidate key :=
  let (_, next, emitted) :=
    Decision.run appConfig.toServerConfig action document
  { document := next
    outputs := emitted.map .message
    continuations }

def selectedWorkCandidate (appConfig : Resonate.Config) (item : WorkItem)
    (now : Time) (rest : List PendingEntry)
    (key : DocumentKey) (document : Document key) :
    Option (Candidate key) :=
  match item with
  | .promiseTimeout id =>
      if h : DocumentKey.origin id.origin = key then
        some ((workCandidate appConfig (h ▸ document)
          (Decision.processPromiseTimeout id now) rest).cast h)
      else none
  | .callback req =>
      if h : DocumentKey.origin req.awaited.origin = key then
        some ((workCandidate appConfig (h ▸ document)
          (Decision.processCallback req now) rest).cast h)
      else none
  | .listener req =>
      if h : DocumentKey.origin req.awaited.origin = key then
        some ((workCandidate appConfig (h ▸ document)
          (Decision.processListener req now) rest).cast h)
      else none
  | .taskLeaseTimeout id =>
      if h : DocumentKey.origin id.origin = key then
        some ((workCandidate appConfig (h ▸ document)
          (Decision.processLeaseTimeout id now) rest).cast h)
      else none
  | .taskRetryTimeout id =>
      if h : DocumentKey.origin id.origin = key then
        some ((workCandidate appConfig (h ▸ document)
          (Decision.processRetryTimeout id now) rest).cast h)
      else none
  | .scheduleTimeout id =>
      if h : DocumentKey.schedule id = key then
        let (occurrences, next, emitted) :=
          Decision.run appConfig.toServerConfig
            (Decision.processSchedule id now) (h ▸ document)
        some (({
          document := next
          outputs := emitted.map .message
          continuations := rest ++
            occurrences.filterMap fun
              | .occurrence request instant =>
                  some (.occurrence request instant)
              | _ => none
        } : Candidate (.schedule id)).cast h)
      else none
  | .occurrence req instant =>
      if h : DocumentKey.origin req.id.origin = key then
        some ((workCandidate appConfig (h ▸ document)
          (Decision.processOccurrence req instant) rest).cast h)
      else none

def singleState (key : DocumentKey) (document : Document key) : State :=
  { store := ({} : Resonate.Store).write key document }

/-- Proof-facing logical result of the independently computed concrete
request decision. -/
def selectedExternal (appConfig : Resonate.Config) (call : Call)
    (key : DocumentKey) (document : Document key) :
    State × List Output :=
  match selectedExternalCandidate appConfig call key document with
  | some candidate =>
      ({ store := ({} : Resonate.Store).write key candidate.document
         workflow := { pending := pendingWorkflow candidate.continuations } },
       candidate.outputs)
  | none => (singleState key document, [])

/-- Proof-facing logical result of an independently computed concrete work
decision. -/
def selectedWork (appConfig : Resonate.Config) (item : WorkItem)
    (now : Time) (rest : List PendingEntry)
    (key : DocumentKey) (document : Document key) :
    State × List Output :=
  match selectedWorkCandidate appConfig item now rest key document with
  | some candidate =>
      ({ store := ({} : Resonate.Store).write key candidate.document
         workflow := { pending := pendingWorkflow candidate.continuations } },
       candidate.outputs)
  | none => (singleState key document, [])

def selectScanWork (appConfig : Resonate.Config) (key : DocumentKey)
    (now : Time) (rest : List PendingEntry) (document : Document key) :
    Option (Candidate key) :=
  match key with
  | .origin origin =>
      match (Decision.originWork origin document now).head? with
      | none => none
      | some item =>
          selectedWorkCandidate appConfig item now rest (.origin origin) document
  | .schedule id =>
      match document with
      | some schedule =>
          if schedule.nextRunAt ≤ now then
            selectedWorkCandidate appConfig (.scheduleTimeout id)
              now rest (.schedule id) document
          else none
      | none => none

def selectScan (appConfig : Resonate.Config) (key : DocumentKey)
    (now : Time) (rest : List PendingEntry) (document : Document key) :
    Option (Candidate key) :=
  match selectScanWork appConfig key now rest document with
  | some candidate => some candidate
  | none =>
      if (documentDeadline? key document now).isSome then
        some { document, outputs := [], continuations := rest }
      else
        none

theorem selectScan_origin_some
    (appConfig : Resonate.Config) (origin : String) (now : Time)
    (rest : List PendingEntry) (document : OriginDocument origin)
    (candidate : Candidate (.origin origin))
    (hselect :
      selectScanWork appConfig (.origin origin) now rest document =
        some candidate) :
    ∃ item,
      item ∈ Decision.originWork origin document now ∧
      let result := selectedWork appConfig item now rest
        (.origin origin) document
      candidate.document = result.1.store.read (.origin origin) ∧
      candidate.outputs = result.2 ∧
      candidate.continuations =
        result.1.workflow.pending.map PendingEntry.fromWorkflow := by
  cases hhead : (Decision.originWork origin document now).head? with
  | none =>
      simp only [selectScanWork] at hselect
      rw [hhead] at hselect
      contradiction
  | some item =>
      simp only [selectScanWork] at hselect
      rw [hhead] at hselect
      refine ⟨item, ?_, ?_⟩
      obtain ⟨remaining, hitems⟩ := List.head?_eq_some_iff.mp hhead
      rw [hitems]
      · exact List.mem_cons_self
      · simp [selectedWork, hselect]

theorem selectScan_schedule_some
    (appConfig : Resonate.Config) (id : ServerModel.Ident) (now : Time)
    (rest : List PendingEntry) (document : ScheduleDocument id)
    (candidate : Candidate (.schedule id))
    (hselect :
      selectScanWork appConfig (.schedule id) now rest document =
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
      simp only [selectScanWork] at hselect
      rw [hdocument] at hselect
      contradiction
  | some schedule =>
      subst document
      simp only [selectScanWork] at hselect
      by_cases hdue : schedule.nextRunAt ≤ now
      · simp only [if_pos hdue] at hselect
        refine ⟨schedule, rfl, hdue, ?_⟩
        simp [selectedWork, hselect]
      · simp only [if_neg hdue] at hselect
        contradiction

def select (appConfig : Resonate.Config) (flight : Flight)
    (loaded : Option (Document flight.key × Version)) :
    Option (Candidate flight.key) :=
  let document := loaded.map (·.1) |>.getD (emptyDocument flight.key)
  match flight.transaction with
  | .external call =>
      selectedExternalCandidate appConfig call flight.key document
  | .work item now rest =>
      selectedWorkCandidate appConfig item now rest flight.key document
  | .sweep timer now rest =>
      if h : timer.target.key = flight.key then
        h ▸ selectScan appConfig timer.target.key now rest
          (h.symm ▸ document)
      else none

def writeCandidate (node : Node) (flight : Flight)
    (loaded : Option (Document flight.key × Version))
    (candidate : Candidate flight.key) :
    Result Pid Local Msg :=
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

def finishNode (node : Node) (flight : Flight) : Node :=
  let wheel :=
    match flight.fired with
    | some _ => node.wheel.finishOne
    | none => node.wheel
  { node with
    pending := flight.continuations ++ node.pending
    wheel }

def finishFlight (node : Node) (flight : Flight) :
    Result Pid Local Msg :=
  { state := .node (finishNode node flight)
    send := sendOutputs flight.selected }

def continueCleanup (node : Node) (flight : Flight) :
    Result Pid Local Msg :=
  let finished := finishNode node flight
  match flight.cleanup with
  | [] =>
      { state := .node finished
        send := sendOutputs flight.selected }
  | keys =>
      let (next, request) :=
        finished.awaitControl (.cleanup flight.selected) (.deleteTimers keys)
      { state := .node next, send := [request] }

def cleanupFlight (flight : Flight) (fired : TimerKey) : Flight :=
  match flight.transaction with
  | .sweep _ _ rest =>
      { flight with
        continuations :=
          if flight.attempt = 0 then rest else flight.continuations
        cleanup := [fired] }
  | .external _ | .work _ _ _ =>
      { flight with cleanup := [fired] }

@[simp] theorem cleanupFlight_cleanup (flight : Flight) (fired : TimerKey) :
    (cleanupFlight flight fired).cleanup = [fired] := by
  cases htransaction : flight.transaction <;>
    simp [cleanupFlight, htransaction]

def decide (appConfig : Resonate.Config) (node : Node) (flight : Flight)
    (loaded : Option (Document flight.key × Version)) :
    Result Pid Local Msg :=
  match select appConfig flight loaded with
  | none =>
      match flight.fired with
      | none => { state := .node node, send := [] }
      | some fired =>
          continueCleanup node (cleanupFlight flight fired)
  | some candidate =>
      match timerForDocument flight.key candidate.document
          flight.transaction.logicalTime node.nextTimerToken flight.address with
      | none => writeCandidate node flight loaded candidate
      | some timer =>
          let arming : Flight := {
            flight with
            loaded
            document := some candidate.document
            selected := candidate.outputs
            continuations := candidate.continuations
            phase := .arming
            armed := some timer
          }
          let node := { node with nextTimerToken := node.nextTimerToken + 1 }
          let (nextNode, request) := node.await arming (.armTimer timer)
          { state := .node nextNode, send := [request] }

def retry (config : Config) (node : Node) (flight : Flight) :
    Result Pid Local Msg :=
  if flight.attempt < config.retries then
    let loading : Flight := {
      flight with
      loaded := none
      document := none
      selected := []
      armed := none
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
  if expectedVersion != store.version key then
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

def start (appConfig : Resonate.Config) (node : Node) (transaction : Transaction)
    (key : DocumentKey) (address : Addr := "")
    (fired : Option TimerKey := none) : Result Pid Local Msg :=
  let flight : Flight := { key, transaction, address, fired }
  match node.cacheRead key with
  | some value =>
      decide appConfig node flight (some (value.document, value.version))
  | none =>
      let (next, request) := node.await flight (.get key)
      { state := .node next, send := [request] }

def pureResponse (now : Time) : Request → Response
  | .promiseRegisterCallback _ =>
      .promiseRegisterCallback { status := 400 }
  | .promiseSearch req =>
      .promiseSearch (Decision.promiseSearch req now)
  | .scheduleSearch req =>
      .scheduleSearch (Decision.scheduleSearch req now)
  | .taskFence _ => .taskFence { status := 400 }
  | .taskHeartbeat req =>
      if req.tasks.isEmpty then .taskHeartbeat { status := 200 }
      else .taskHeartbeat { status := 400 }
  | .taskSuspend _ => .taskSuspend { status := 400 }
  | .taskFulfill _ => .taskFulfill { status := 400 }
  | .taskSearch req =>
      .taskSearch (Decision.taskSearch req now)
  | request => unavailableResponse request

def pureExternal (_appConfig : Resonate.Config) (node : Node) (call : Call) :
    Result Pid Local Msg :=
  { state := .node node
    send := sendOutputs
      [.response call.client call.id
        (pureResponse call.requestedAt call.request)] }

def cleanupKeys (node : Node) (flight : Flight) : List TimerKey :=
  let predecessor :=
    match node.previousArmed? flight with
    | some key => if some key == flight.fired then [] else [key]
    | none => []
  predecessor ++ flight.fired.toList

def committedFlight (node : Node) (flight : Flight) :
    Result Pid Local Msg :=
  let cleanup := cleanupKeys node flight
  continueCleanup (node.noteArmed flight) { flight with cleanup }

def latestAnnouncement (values : List Announcement) : Time :=
  values.foldl (fun latest value => max latest value.announcedAt) 0

def liveAnnouncementIds
    (values : List Announcement) (now ttl : Time) : List Addr :=
  let fleetAt := max now (latestAnnouncement values)
  (values.filter fun value => fleetAt ≤ value.announcedAt + ttl).map (·.id)

def beginMembershipRefresh (node : Node) (address : Addr) (now : Time) :
    Result Pid Local Msg :=
  let announcement : Announcement := {
    id := address
    url := address
    announcedAt := now
  }
  let (next, request) :=
    node.awaitControl (.announced now) (.announce announcement)
  { state := .node next, send := [request] }

def beginTimerList (node : Node) (config : Config)
    (now : Time) (kind : ListingKind) : Result Pid Local Msg :=
  let through := now + config.loadAhead
  let (next, request) :=
    node.awaitControl (.timerList now through kind) (.listTimers through)
  { state := .node {
      next with wheel := { next.wheel with listing := some kind } }
    send := [request] }

def refreshEnded (node : Node) (config : Config) (now : Time) :
    Result Pid Local Msg :=
  beginTimerList { node with nextHeartbeat := some (now + config.heartbeat) }
    config now .initial

def step (appConfig : Resonate.Config) (config : Config) (pid : Pid)
    (localState : Local) (now : Time) (event : Event Pid Msg) :
    Outcomes (Result Pid Local Msg) :=
  match pid, localState, event with
  | .node address, .node node, .receive .outside (.request call) =>
      if !node.flights.isEmpty || !node.controls.isEmpty then
        Outcomes.one { state := .node node, send := [] }
      else
        match (Transaction.external call).key? with
        | some key =>
            let target := TimerTarget.ofDocumentKey key
            if node.membership.owns address now config.nodeTtl target then
              Outcomes.one
                (start appConfig node (.external call) key address)
            else
              Outcomes.one {
                state := .node node
                send := sendOutputs [Resonate.unavailable call]
              }
        | none => Outcomes.one (pureExternal appConfig node call)
  | .node address, .node node, .timeout =>
      if !node.flights.isEmpty || !node.controls.isEmpty then
        Outcomes.one { state := .node node, send := [] }
      else
        match node.pending with
        | entry :: rest =>
            let transaction :=
              match entry with
              | .occurrence request instant =>
                  Transaction.work (.occurrence request instant) instant rest
            Outcomes.one (start appConfig {
              node with pending := [] }
              transaction entry.key address)
        | [] =>
            if node.nextHeartbeat.all (· ≤ now) then
              Outcomes.one (beginMembershipRefresh node address now)
            else
              let wheel := node.wheel.takeDue now config.fireConcurrency
              match wheel.beginOne with
              | some (timer, wheel) =>
                  let node := { node with wheel }
                  if node.membership.owns address now config.nodeTtl
                      timer.target then
                    Outcomes.one
                      (start appConfig node (.sweep timer now [])
                        timer.target.key address (some timer))
                  else
                    Outcomes.one {
                      state := .node {
                        node with wheel := node.wheel.finishOne }
                      send := []
                    }
              | none =>
                  let currentBucket := bucketOf config.bucketWidth now
                  if node.wheel.closedThrough < currentBucket then
                    Outcomes.one
                      (beginTimerList { node with wheel } config now
                        (.relist node.wheel.closedThrough))
                  else if node.wheel.loadedThrough < now + config.loadAhead then
                    Outcomes.one
                      (beginTimerList { node with wheel } config now .extend)
                  else
                    Outcomes.one { state := .node { node with wheel }, send := [] }
  | .node _, .node node,
      .receive .store (.storeReply { op, payload := .got key loaded }) =>
      let (flight, next) := node.takeFlight op
      match flight with
      | some flight =>
          if h : key = flight.key then
            match flight.phase with
            | .loading =>
                let loaded' := h ▸ loaded
                let cached :=
                  match loaded' with
                  | some (document, version) =>
                      next.cachePut flight.key { document, version }
                  | none => next.cacheInvalidate flight.key
                Outcomes.one (decide appConfig cached flight loaded')
            | .arming | .writing | .deleting =>
                Outcomes.one {
                  state := .node {
                    next with flights := (op, flight) :: next.flights }
                  send := []
                }
          else
            Outcomes.one {
              state := .node {
                next with flights := (op, flight) :: next.flights }
              send := []
            }
      | none => Outcomes.one { state := .node node, send := [] }
  | .node _, .node node,
      .receive .store (.storeReply { op, payload := .written }) =>
      let (flight, next) := node.takeFlight op
      match flight with
      | some flight =>
          match flight.phase with
          | .writing =>
              Outcomes.one (committedFlight next flight)
          | .loading | .arming | .deleting =>
              Outcomes.one {
                state := .node {
                  next with flights := (op, flight) :: next.flights }
                send := []
              }
      | none => Outcomes.one { state := .node node, send := [] }
  | .node _, .node node,
      .receive .store (.storeReply { op, payload := .done }) =>
      let (flight, next) := node.takeFlight op
      match flight with
      | some flight =>
          match flight.phase with
          | .arming =>
              match flight.document with
              | none => Outcomes.one { state := .node next, send := [] }
              | some document =>
                  let writing := { flight with phase := .writing }
                  let (nextNode, request) :=
                    next.await writing
                      (.put flight.key document (flight.loaded.map (·.2)))
                  Outcomes.one { state := .node nextNode, send := [request] }
          | .deleting => Outcomes.one (continueCleanup next flight)
          | .loading | .writing =>
              Outcomes.one {
                state := .node {
                  next with flights := (op, flight) :: next.flights }
                send := []
              }
      | none =>
          let (control, next) := node.takeControl op
          match control with
          | some (.announced instant) =>
              let (nextNode, request) :=
                next.awaitControl (.announcements instant) .listAnnouncements
              Outcomes.one { state := .node nextNode, send := [request] }
          | some (.membershipWrite instant) =>
              Outcomes.one (refreshEnded next config instant)
          | some (.cleanup outputs) =>
              Outcomes.one {
                state := .node next
                send := sendOutputs outputs
              }
          | some (.timerList _ _ _) | some (.announcements _)
          | some (.membership _ _) | none =>
              Outcomes.one { state := .node next, send := [] }
  | .node _, .node node,
      .receive .store
        (.storeReply { op, payload := .announcements values }) =>
      let (control, next) := node.takeControl op
      match control with
      | some (.announcements instant) =>
          let live := liveAnnouncementIds values instant config.nodeTtl
          let (nextNode, request) :=
            next.awaitControl (.membership instant live) .getMembership
          Outcomes.one { state := .node nextNode, send := [request] }
      | _ => Outcomes.one { state := .node next, send := [] }
  | .node address, .node node,
      .receive .store
        (.storeReply { op, payload := .membership membership version }) =>
      let (control, next) := node.takeControl op
      match control with
      | some (.membership instant live) =>
          let view : MembershipView := {
            epoch := membership.epoch
            members := membership.members
            version
            lastRead := instant
            readAny := true
          }
          let next := { next with membership := view }
          if live == membership.members then
            Outcomes.one (refreshEnded next config instant)
          else
            let proposed : MembershipConfig := {
              epoch := membership.epoch + 1
              members := live
            }
            let (nextNode, request) :=
              next.awaitControl (.membershipWrite instant)
                (.putMembership version proposed)
            Outcomes.one { state := .node nextNode, send := [request] }
      | _ => Outcomes.one { state := .node next, send := [] }
  | .node address, .node node,
      .receive .store (.storeReply { op, payload := .timers keys }) =>
      let (control, next) := node.takeControl op
      match control with
      | some (.timerList instant through kind) =>
          let wheel :=
            next.wheel.load next.membership address instant config.nodeTtl
              through keys
          let wheel :=
            match kind with
            | .relist closed =>
                { wheel with
                  closedThrough :=
                    max wheel.closedThrough
                      (bucketOf config.bucketWidth instant) }
            | .initial | .extend => wheel
          Outcomes.one { state := .node { next with wheel }, send := [] }
      | _ => Outcomes.one { state := .node next, send := [] }
  | .node _, .node node,
      .receive .store (.storeReply { op, payload := .conflict }) =>
      -- A conflict is ambiguous once a duplicate conditional put can be
      -- refused after the first copy landed. Retrying would decide again
      -- against a workflow that may already have advanced. Restoring the
      -- flight keeps that workflow in place; a later written or failed
      -- reply for the same operation still matches it.
      let (flight, next) := node.takeFlight op
      match flight with
      | some flight =>
          Outcomes.one {
            state := .node {
              next with flights := (op, flight) :: next.flights }
            send := []
          }
      | none =>
          let (control, next) := node.takeControl op
          match control with
          | some (.membershipWrite instant) =>
              Outcomes.one (refreshEnded next config instant)
          | _ => Outcomes.one { state := .node next, send := [] }
  | .node _, .node node,
      .receive .store (.storeReply { op, payload := .failed }) =>
      let (flight, next) := node.takeFlight op
      match flight with
      | some flight =>
          match flight.phase with
          | .deleting => Outcomes.one (continueCleanup next flight)
          | .loading | .arming | .writing =>
              Outcomes.one {
                state := .node (next.cacheInvalidate flight.key)
                send := sendOutputs (failureOutputs flight.transaction)
              }
      | none =>
          let (control, next) := node.takeControl op
          match control with
          | some (.announced instant) | some (.announcements instant)
          | some (.membershipWrite instant) =>
              Outcomes.one {
                state := .node {
                  next with
                  nextHeartbeat := some (instant + config.heartbeat) }
                send := []
              }
          | some (.membership instant _) =>
              Outcomes.one {
                state := .node {
                  next with
                  nextHeartbeat := some (instant + config.heartbeat) }
                send := []
              }
          | some (.timerList _ _ _) =>
              Outcomes.one {
                state := .node {
                  next with wheel := { next.wheel with listing := none } }
                send := []
              }
          | some (.cleanup outputs) =>
              Outcomes.one {
                state := .node next
                send := sendOutputs outputs
              }
          | none => Outcomes.one { state := .node next, send := [] }
  | .store, .store store,
      .receive sender (.storeRequest { op, payload := .get key }) =>
      Outcomes.one {
        state := .store store
        send := [(sender, .storeReply {
          op, payload := .got key (store.read key) })]
      }
  | .store, .store store,
      .receive sender (.storeRequest { op, payload := .armTimer timer }) =>
      Outcomes.one {
        state := .store { store with timers := store.timers.arm timer }
        send := [(sender, .storeReply { op, payload := .done })]
      }
  | .store, .store store,
      .receive sender (.storeRequest { op, payload := .deleteTimer timer }) =>
      Outcomes.one {
        state := .store { store with timers := store.timers.delete timer }
        send := [(sender, .storeReply { op, payload := .done })]
      }
  | .store, .store store,
      .receive sender (.storeRequest { op, payload := .deleteTimers timers }) =>
      Outcomes.one {
        state := .store {
          store with
          timers := timers.foldl TimerObjects.delete store.timers }
        send := [(sender, .storeReply { op, payload := .done })]
      }
  | .store, .store store,
      .receive sender (.storeRequest { op, payload := .listTimers through }) =>
      Outcomes.one {
        state := .store store
        send := [(sender, .storeReply {
          op, payload := .timers (store.timers.listThrough through) })]
      }
  | .store, .store store,
      .receive sender (.storeRequest { op, payload := .announce announcement }) =>
      Outcomes.one {
        state := .store {
          store with
          membership := store.membership.announce announcement }
        send := [(sender, .storeReply { op, payload := .done })]
      }
  | .store, .store store,
      .receive sender (.storeRequest { op, payload := .listAnnouncements }) =>
      Outcomes.one {
        state := .store store
        send := [(sender, .storeReply {
          op, payload := .announcements store.membership.announcements })]
      }
  | .store, .store store,
      .receive sender (.storeRequest { op, payload := .getMembership }) =>
      Outcomes.one {
        state := .store store
        send := [(sender, .storeReply {
          op
          payload := .membership store.membership.configuration
            store.membership.version })]
      }
  | .store, .store store,
      .receive sender
        (.storeRequest { op, payload := .putMembership expected next }) =>
      match store.membership.putConfig expected next with
      | some membership =>
          Outcomes.one {
            state := .store { store with membership }
            send := [(sender, .storeReply { op, payload := .done })]
          }
      | none =>
          Outcomes.one {
            state := .store store
            send := [(sender, .storeReply { op, payload := .conflict })]
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

def boundaryTrace (execution : Execution (model nodes appConfig)) :
    List Resonate.BoundaryEvent :=
  (Rover.trace execution).filterMap boundaryEvent

def ValidBoundaryTrace (nodes : List Addr) (appConfig : Resonate.Config)
    (config : Config) (events : List Resonate.BoundaryEvent) : Prop :=
  ∃ execution,
    Behavior (model nodes appConfig) config execution ∧
    boundaryTrace execution = events

end Resonate.Concrete

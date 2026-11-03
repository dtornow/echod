import Rover
import «concrete».ProcessStore
import «concrete».Internal

/-!
# The node process

A node keeps its continuations locally and talks to the store only through
GET and conditional PUT payloads. It derives document ownership from a shared
ordered membership it reads from the store; nodes never exchange ownership
messages. Its timer wheel is only a local index of durable timer keys;
deleting a wheel entry cannot delete the durable key.
-/

namespace Resonate.Concrete

open Rover

/-- The one timer key a node associates with a document version.  It is a
cache hint for predecessor cleanup, never the source of timer safety. -/
structure ArmedEntry where
  target : DocumentKey
  timer : TimerKey
  version : Nat
  deriving Repr

/-- Start of the time bucket containing `instant`. -/
def bucketOf (bucketWidth instant : Time) : Time :=
  let width := max bucketWidth 1
  instant / width * width

def minimumTime? : List Time → Option Time
  | [] => none
  | first :: rest => some (rest.foldl min first)

def OriginObject.deadlines {origin : String}
    (object : OriginObject origin) (now : Time) : List Time :=
  let promise :=
    if object.promise.state == .pending then
      [object.promise.timeoutAt]
    else if !object.promise.callbacks.isEmpty ||
        !object.promise.listeners.isEmpty then
      [now]
    else
      []
  let task :=
    match object.task with
    | none => []
    | some task =>
        (if task.state == .acquired then task.leaseTimeoutAt.toList else []) ++
        (if task.state == .pending then task.retryTimeoutAt.toList else [])
  promise ++ task

def documentDeadline?
    (key : DocumentKey) (document : Document key) (now : Time) :
    Option Time :=
  match key with
  | .origin _ =>
      minimumTime?
        (document.flatMap fun object => OriginObject.deadlines object now)
  | .schedule _ =>
      document.map (·.nextRunAt)

def timerForDocument
    (key : DocumentKey) (document : Document key) (now : Time)
    (token : TimerToken) (armedBy : Addr) : Option TimerKey :=
  (documentDeadline? key document now).map fun deadline =>
    { deadline
      target := TimerTarget.ofDocumentKey key
      token
      armedBy }

/-- FNV-1a over UTF-8, matching echod's stable ownership hash. -/
def fnv1a (value : String) : UInt64 :=
  value.toUTF8.foldl
    (fun hash byte => (hash ^^^ byte.toUInt64) * 0x00000100000001b3)
    0xcbf29ce484222325

def owner? (members : List Addr) (target : TimerTarget) : Option Addr :=
  if h : members.length = 0 then
    none
  else
    members[(fnv1a target.partitionKey).toNat.mod members.length]?

structure MembershipView where
  members : List Addr := []
  version : Nat := 0
  lastRead : Time := 0
  readAny : Bool := false
  deriving Repr

def MembershipView.fresh
    (view : MembershipView) (now ttl : Time) : Bool :=
  view.readAny && now ≤ view.lastRead + ttl

def MembershipView.owns
    (view : MembershipView) (me : Addr) (now ttl : Time)
    (target : TimerTarget) : Bool :=
  view.fresh now ttl && owner? view.members target == some me

/-- Node-local index of durable keys.  `loadedThrough` is the look-ahead
horizon; `closedThrough` records the last bucket that received its mandatory
second listing, which closes the gap that can occur while another node arms a
key in a bucket already loaded by this node. -/
structure TimerWheel where
  entries : List TimerKey := []
  loadedThrough : Time := 0
  closedThrough : Time := 0
  deriving Repr

def TimerWheel.insert (wheel : TimerWheel) (key : TimerKey) : TimerWheel :=
  if wheel.entries.contains key then wheel
  else { wheel with entries := wheel.entries ++ [key] }

def TimerWheel.load
    (wheel : TimerWheel) (view : MembershipView) (me : Addr)
    (now ttl through : Time) (keys : List TimerKey) : TimerWheel :=
  let owned :=
    keys.filter fun key =>
      key.deadline ≤ through && view.owns me now ttl key.target
  { wheel with
    entries := (owned.foldl TimerWheel.insert wheel).entries
    loadedThrough := max wheel.loadedThrough through }

def TimerWheel.due (wheel : TimerWheel) (now : Time) : List TimerKey :=
  wheel.entries.filter (·.deadline ≤ now)

/-- Remove and return the due entry with the earliest deadline. -/
def TimerWheel.next? (wheel : TimerWheel) (now : Time) :
    Option (TimerKey × TimerWheel) :=
  match wheel.due now with
  | [] => none
  | first :: rest =>
      let key := rest.foldl
        (fun best key => if key.deadline < best.deadline then key else best) first
      some (key, { wheel with entries := wheel.entries.filter (· != key) })

/-- A dependent cache entry: the value's type is fixed by its key. -/
structure CacheEntry where
  key : DocumentKey
  value : Versioned key

inductive Control where
  | announced (now : Time)
  | announcements (now : Time)
  | membership (now : Time) (live : List Addr)
  | membershipWrite (now : Time)
  | timerList (now through : Time) (relist : Bool)
  | cleanup (outputs : List Output)
  deriving Repr

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

/-- The candidate `make` builds, when it decides `key`. -/
def candidateAt {decided : DocumentKey} (key : DocumentKey) (document : Document key)
    (make : Document decided → Candidate decided) : Option (Candidate key) :=
  if h : decided = key then some ((make (h ▸ document)).cast h) else none

def selectedExternalCandidate (appConfig : Resonate.Config) (call : Call)
    (key : DocumentKey) (document : Document key) :
    Option (Candidate key) :=
  let run {decided : DocumentKey} {α : Type} (action : Decision.Handler decided α)
      (wrap : α → Response) :=
    candidateAt key document fun document =>
      externalCandidate appConfig call document action wrap
  match call.request with
  | .promiseGet req => run (Decision.promiseGet req call.requestedAt) .promiseGet
  | .promiseCreate req =>
      run (Decision.promiseCreate (origin := req.id.origin) req call.requestedAt) .promiseCreate
  | .promiseSettle req =>
      run (Decision.promiseSettle (origin := req.id.origin) req call.requestedAt) .promiseSettle
  | .promiseRegisterCallback req =>
      run (Decision.promiseRegisterCallback req call.requestedAt) .promiseRegisterCallback
  | .promiseRegisterListener req =>
      run (Decision.promiseRegisterListener req call.requestedAt) .promiseRegisterListener
  | .scheduleGet req => run (Decision.scheduleGet req call.requestedAt) .scheduleGet
  | .scheduleCreate req => run (Decision.scheduleCreate req call.requestedAt) .scheduleCreate
  | .scheduleDelete req => run (Decision.scheduleDelete req call.requestedAt) .scheduleDelete
  | .taskGet req => run (Decision.taskGet req call.requestedAt) .taskGet
  | .taskCreate req => run (Decision.taskCreate req call.requestedAt) .taskCreate
  | .taskAcquire req => run (Decision.taskAcquire req call.requestedAt) .taskAcquire
  | .taskFence req => run (Decision.taskFence req call.requestedAt) .taskFence
  | .taskHeartbeat req =>
      match req.tasks with
      | [] => none
      | first :: _ =>
          run (Decision.taskHeartbeat first.id.origin req call.requestedAt) .taskHeartbeat
  | .taskSuspend req => run (Decision.taskSuspend req call.requestedAt) .taskSuspend
  | .taskFulfill req => run (Decision.taskFulfill req call.requestedAt) .taskFulfill
  | .taskRelease req => run (Decision.taskRelease req call.requestedAt) .taskRelease
  | .taskHalt req => run (Decision.taskHalt req call.requestedAt) .taskHalt
  | .taskContinue req => run (Decision.taskContinue req call.requestedAt) .taskContinue
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
  let run {decided : DocumentKey} {α : Type} (action : Decision.Handler decided α) :=
    candidateAt key document fun document =>
      workCandidate appConfig document action rest
  match item with
  | .promiseTimeout id => run (Decision.processPromiseTimeout id now)
  | .callback req => run (Decision.processCallback req now)
  | .listener req => run (Decision.processListener req now)
  | .taskLeaseTimeout id => run (Decision.processLeaseTimeout id now)
  | .taskRetryTimeout id => run (Decision.processRetryTimeout id now)
  | .scheduleTimeout id =>
      candidateAt key document fun document =>
        let (occurrences, next, emitted) :=
          Decision.run appConfig.toServerConfig (Decision.processSchedule id now) document
        { document := next
          outputs := emitted.map .message
          continuations := rest ++
            occurrences.filterMap fun
              | .occurrence request instant => some (.occurrence request instant)
              | _ => none }
  | .occurrence req instant => run (Decision.processOccurrence req instant)

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
  { node with pending := flight.continuations ++ node.pending }

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
    announcedAt := now
  }
  let (next, request) :=
    node.awaitControl (.announced now) (.announce announcement)
  { state := .node next, send := [request] }

def beginTimerList (node : Node) (config : Config)
    (now : Time) (relist : Bool) : Result Pid Local Msg :=
  let through := now + config.loadAhead
  let (next, request) :=
    node.awaitControl (.timerList now through relist) (.listTimers through)
  { state := .node next, send := [request] }

def refreshEnded (node : Node) (config : Config) (now : Time) :
    Result Pid Local Msg :=
  beginTimerList { node with nextHeartbeat := some (now + config.heartbeat) }
    config now false

def nodeStep (appConfig : Resonate.Config) (config : Config) (address : Addr)
    (node : Node) (now : Time) (event : Event Pid Msg) :
    Outcomes (Result Pid Local Msg) :=
  match event with
  | .receive .outside (.request call) =>
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
  | .timeout =>
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
              match node.wheel.next? now with
              | some (timer, wheel) =>
                  let node := { node with wheel }
                  if node.membership.owns address now config.nodeTtl
                      timer.target then
                    Outcomes.one
                      (start appConfig node (.sweep timer now [])
                        timer.target.key address (some timer))
                  else
                    Outcomes.one { state := .node node, send := [] }
              | none =>
                  let currentBucket := bucketOf config.bucketWidth now
                  if node.wheel.closedThrough < currentBucket then
                    Outcomes.one (beginTimerList node config now true)
                  else if node.wheel.loadedThrough < now + config.loadAhead then
                    Outcomes.one (beginTimerList node config now false)
                  else
                    Outcomes.one { state := .node node, send := [] }
  | .receive .store (.storeReply { op, payload := .got key loaded }) =>
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
  | .receive .store (.storeReply { op, payload := .written }) =>
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
  | .receive .store (.storeReply { op, payload := .done }) =>
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
  | .receive .store
        (.storeReply { op, payload := .announcements values }) =>
      let (control, next) := node.takeControl op
      match control with
      | some (.announcements instant) =>
          let live := liveAnnouncementIds values instant config.nodeTtl
          let (nextNode, request) :=
            next.awaitControl (.membership instant live) .getMembership
          Outcomes.one { state := .node nextNode, send := [request] }
      | _ => Outcomes.one { state := .node next, send := [] }
  | .receive .store
        (.storeReply { op, payload := .membership membership version }) =>
      let (control, next) := node.takeControl op
      match control with
      | some (.membership instant live) =>
          let view : MembershipView := {
            members := membership.members
            version
            lastRead := instant
            readAny := true
          }
          let next := { next with membership := view }
          if live == membership.members then
            Outcomes.one (refreshEnded next config instant)
          else
            let proposed : MembershipConfig := { members := live }
            let (nextNode, request) :=
              next.awaitControl (.membershipWrite instant)
                (.putMembership version proposed)
            Outcomes.one { state := .node nextNode, send := [request] }
      | _ => Outcomes.one { state := .node next, send := [] }
  | .receive .store (.storeReply { op, payload := .timers keys }) =>
      let (control, next) := node.takeControl op
      match control with
      | some (.timerList instant through relist) =>
          let wheel :=
            next.wheel.load next.membership address instant config.nodeTtl
              through keys
          let wheel :=
            if relist then
              { wheel with
                closedThrough :=
                  max wheel.closedThrough
                    (bucketOf config.bucketWidth instant) }
            else wheel
          Outcomes.one { state := .node { next with wheel }, send := [] }
      | _ => Outcomes.one { state := .node next, send := [] }
  | .receive .store (.storeReply { op, payload := .conflict }) =>
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
  | .receive .store (.storeReply { op, payload := .failed }) =>
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
          | some (.membershipWrite instant) | some (.membership instant _) =>
              Outcomes.one {
                state := .node {
                  next with
                  nextHeartbeat := some (instant + config.heartbeat) }
                send := []
              }
          | some (.timerList _ _ _) =>
              Outcomes.one { state := .node next, send := [] }
          | some (.cleanup outputs) =>
              Outcomes.one {
                state := .node next
                send := sendOutputs outputs
              }
          | none => Outcomes.one { state := .node next, send := [] }
  | _ => Outcomes.one { state := .node node, send := [] }

end Resonate.Concrete

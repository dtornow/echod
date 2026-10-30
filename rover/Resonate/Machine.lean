import «02-abstract».«system»

/-!
# Document-scoped Resonate abstract machine

The global store is a dependent map. Promise/task rows are grouped by origin;
each schedule has a distinct document key and document type. A `Handler key`
receives only `Document key`, so neither bind nor any primitive can cross a
document boundary or inspect the global store.
-/

namespace Resonate

open ServerModel

abbrev PromiseObject := AbstractModel.PromiseObject
abbrev TaskObject := AbstractModel.TaskObject

deriving instance DecidableEq for Value
deriving instance DecidableEq for PromiseRecord
deriving instance DecidableEq for TaskRecord
deriving instance DecidableEq for Schedule
deriving instance DecidableEq for Message
deriving instance DecidableEq for OutboxEntry

/-- The transaction key. Origin documents and schedule documents are distinct
constructors, so a handler for one can never be bound to a handler for the
other. -/
inductive DocumentKey where
  | origin (origin : String)
  | schedule (id : Ident)
  deriving Repr, DecidableEq

/-- A fused promise/task row whose origin is fixed by its type. Only the suffix
is stored; reconstructing its public id necessarily uses the indexed origin. -/
structure OriginObject (origin : String) where
  suffix : String
  promise : PromiseObject
  task : Option TaskObject := none
  deriving Repr

def OriginObject.id (object : OriginObject origin) : Ident :=
  { origin, suffix := object.suffix }

def OriginObject.project (object : OriginObject origin) (now : Nat) :
    OriginObject origin :=
  let promise := object.promise.project now
  { object with promise, task := object.task.map (·.view promise) }

abbrev OriginDocument (origin : String) := List (OriginObject origin)

/-- Schedule contents omit the id: the schedule id is fixed by the document
index and cannot disagree with the stored value. -/
structure ScheduleData (id : Ident) where
  cron : String
  promiseId : Ident
  promiseTimeout : Nat
  promiseParam : Value
  promiseTags : Tags
  nextRunAt : Nat
  lastRunAt : Option Nat := none
  createdAt : Nat
  deriving Repr

def ScheduleData.toSchedule {id : Ident} (data : ScheduleData id) : Schedule :=
  { id
    cron := data.cron
    promiseId := data.promiseId
    promiseTimeout := data.promiseTimeout
    promiseParam := data.promiseParam
    promiseTags := data.promiseTags
    nextRunAt := data.nextRunAt
    lastRunAt := data.lastRunAt
    createdAt := data.createdAt }

def ScheduleData.ofSchedule (schedule : Schedule) :
    ScheduleData schedule.id :=
  { cron := schedule.cron
    promiseId := schedule.promiseId
    promiseTimeout := schedule.promiseTimeout
    promiseParam := schedule.promiseParam
    promiseTags := schedule.promiseTags
    nextRunAt := schedule.nextRunAt
    lastRunAt := schedule.lastRunAt
    createdAt := schedule.createdAt }

abbrev ScheduleDocument (id : Ident) := Option (ScheduleData id)

/-- The document family enforces both document kind and origin membership. -/
def Document : DocumentKey → Type
  | .origin origin => OriginDocument origin
  | .schedule id => ScheduleDocument id

def emptyDocument : (key : DocumentKey) → Document key
  | .origin _ => []
  | .schedule _ => none

/-- A finite dependent map. `keys` is only its finite-domain index; all mutable
application data is behind the dependent `documents` projection. -/
structure Store where
  keys : List DocumentKey := []
  documents : (key : DocumentKey) → Document key := emptyDocument

def Store.read (store : Store) (key : DocumentKey) : Document key :=
  store.documents key

def Store.write (store : Store) (key : DocumentKey) (document : Document key) :
    Store :=
  { keys :=
      if store.keys.contains key then store.keys else store.keys ++ [key]
    documents := fun other =>
      if h : other = key then h.symm ▸ document else store.documents other }

@[simp] theorem Store.read_write_same (store : Store) (key : DocumentKey)
    (document : Document key) :
    (store.write key document).read key = document := by
  simp [Store.write, Store.read]

@[simp] theorem Store.read_write_other (store : Store) (key other : DocumentKey)
    (document : Document key) (h : other ≠ key) :
    (store.write key document).read other = store.read other := by
  simp [Store.write, Store.read, h]

@[simp] theorem Store.key_mem_write (store : Store) (key : DocumentKey)
    (document : Document key) :
    key ∈ (store.write key document).keys := by
  by_cases h : key ∈ store.keys <;> simp [Store.write, h]

def Store.originKeys (store : Store) : List String :=
  store.keys.filterMap fun
    | .origin origin => some origin
    | .schedule _ => none

def Store.scheduleKeys (store : Store) : List Ident :=
  store.keys.filterMap fun
    | .origin _ => none
    | .schedule id => some id

inductive WorkItem where
  | promiseTimeout (id : Ident)
  | callback (req : PromiseRegisterCallbackReq)
  | listener (req : PromiseRegisterListenerReq)
  | taskLeaseTimeout (id : Ident)
  | taskRetryTimeout (id : Ident)
  | scheduleTimeout (id : Ident)
  | occurrence (req : PromiseCreateReq) (time : Nat)
  deriving Repr

/-- The only abstract local workflow state is genuine cross-document schedule
occurrence work. A timeout chooses eligible document work directly, without
storing generic discovery state. -/
structure WorkflowEntry where
  request : PromiseCreateReq
  instant : Nat
  deriving Repr

def WorkflowEntry.item (entry : WorkflowEntry) : WorkItem :=
  .occurrence entry.request entry.instant

def WorkflowEntry.key (entry : WorkflowEntry) : DocumentKey :=
  .origin entry.request.id.origin

/-- Process-local cross-document occurrence continuations. -/
structure WorkflowState where
  pending : List WorkflowEntry := []
  deriving Repr

/-- Rover's process state separates the global dependent store from local
workflow continuations. -/
structure State where
  store : Store := {}
  workflow : WorkflowState := {}

def State.init : State := {}

def State.originDocument (state : State) (origin : String) :
    OriginDocument origin :=
  state.store.read (.origin origin)

def State.scheduleDocument (state : State) (id : Ident) :
    ScheduleDocument id :=
  state.store.read (.schedule id)

def State.withOrigin (state : State) (origin : String)
    (document : OriginDocument origin) : State :=
  { state with store := state.store.write (.origin origin) document }

def State.withSchedule (state : State) (schedule : Schedule) : State :=
  { state with
    store := state.store.write (.schedule schedule.id)
      (some (ScheduleData.ofSchedule schedule)) }

namespace Direct

abbrev ServerConfig := AbstractModel.ServerConfig

structure Env where
  config : ServerConfig := {}

/-- Fixed-key Reader+State+Writer. The state is exactly one document. -/
def Handler (key : DocumentKey) (α : Type) : Type :=
  Env → Document key → α × Document key × List OutboxEntry

instance (key : DocumentKey) : Monad (Handler key) where
  pure value := fun _ document => (value, document, [])
  bind action next := fun env document =>
    let (value, document', emitted₁) := action env document
    let (result, document'', emitted₂) := next value env document'
    (result, document'', emitted₁ ++ emitted₂)

def ask {key : DocumentKey} : Handler key Env :=
  fun env document => (env, document, [])

def get {key : DocumentKey} : Handler key (Document key) :=
  fun _ document => (document, document, [])

def set {key : DocumentKey} (document : Document key) : Handler key Unit :=
  fun _ _ => ((), document, [])

def modify {key : DocumentKey} (f : Document key → Document key) :
    Handler key Unit :=
  fun _ document => ((), f document, [])

def emit {key : DocumentKey} (entry : OutboxEntry) : Handler key Unit :=
  fun _ document => ((), document, [entry])

/-- The only bridge between a handler and the global store. It supplies and
commits precisely the indexed document. -/
def runWith (config : ServerConfig) (key : DocumentKey)
    (action : Handler key α) (store : Store) :
    α × Store × List OutboxEntry :=
  let (value, document, emitted) := action { config } (store.read key)
  (value, store.write key document, emitted)

def run (key : DocumentKey) (action : Handler key α) (store : Store) :
    α × Store × List OutboxEntry :=
  runWith {} key action store

/-- Running a handler frames every other document. -/
theorem runWith_frame (config : ServerConfig) (key other : DocumentKey)
    (action : Handler key α) (store : Store) (h : other ≠ key) :
    (runWith config key action store).2.1.read other = store.read other := by
  exact Store.read_write_other store key other
    (action { config } (store.read key)).2.1 h

def Store.ChangedOnly (key : DocumentKey) (before after : Store) : Prop :=
  ∀ other, other ≠ key → after.read other = before.read other

def Store.AtMostOneDocument (before after : Store) : Prop :=
  (∀ key, after.read key = before.read key) ∨
    ∃ key, Store.ChangedOnly key before after

theorem runWith_changedOnly (config : ServerConfig) (key : DocumentKey)
    (action : Handler key α) (store : Store) :
    Store.ChangedOnly key store (runWith config key action store).2.1 := by
  intro other h
  exact runWith_frame config key other action store h

theorem origin_schedule_ne (origin : String) (id : Ident) :
    DocumentKey.origin origin ≠ DocumentKey.schedule id := by
  intro h
  cases h

def getObject {origin : String} (suffix : String) :
    Handler (.origin origin) (Option (OriginObject origin)) := do
  return (← get).find? (·.suffix == suffix)

def setPromise {origin : String} (suffix : String) (promise : PromiseObject) :
    Handler (.origin origin) Unit :=
  modify fun document =>
    let object :=
      match document.find? (·.suffix == suffix) with
      | some existing => { existing with promise }
      | none => { suffix, promise }
    object :: document.filter (·.suffix != suffix)

def setTask {origin : String} (suffix : String) (task : TaskObject) :
    Handler (.origin origin) Unit :=
  modify fun document =>
    document.map fun object =>
      if object.suffix == suffix then { object with task := some task }
      else object

def setObject {origin : String} (object : OriginObject origin) :
    Handler (.origin origin) Unit :=
  modify fun document =>
    object :: document.filter (·.suffix != object.suffix)

def getSchedule {id : Ident} : Handler (.schedule id) (Option Schedule) := do
  return (← get).map (·.toSchedule)

def setSchedule {id : Ident} (data : ScheduleData id) :
    Handler (.schedule id) Unit :=
  set (some data)

def setScheduleValue {id : Ident} (schedule : Schedule) :
    Handler (.schedule id) Unit :=
  setSchedule {
    cron := schedule.cron
    promiseId := schedule.promiseId
    promiseTimeout := schedule.promiseTimeout
    promiseParam := schedule.promiseParam
    promiseTags := schedule.promiseTags
    nextRunAt := schedule.nextRunAt
    lastRunAt := schedule.lastRunAt
    createdAt := schedule.createdAt
  }

def delSchedule {id : Ident} : Handler (.schedule id) Unit :=
  set none

def setMessage {key : DocumentKey} (address : String) (message : Message) :
    Handler key Unit :=
  emit { address, message }

def setSettled {origin : String} (object : OriginObject origin)
    (promise : PromiseObject) : Handler (.origin origin) Unit := do
  setPromise object.suffix promise
  if promise.state != .pending then
    match object.task with
    | some task =>
        if task.state != .fulfilled then setTask object.suffix task.fulfill
    | none => pure ()

def createPromiseAt {origin : String} (suffix : String) (timeoutAt now : Nat)
    (param : Value) (tags : Tags) :
    Handler (.origin origin) (OriginObject origin) := do
  if timeoutAt > now then
    let promise : PromiseObject :=
      { state := .pending, param, tags, timeoutAt, createdAt := now }
    setPromise suffix promise
    if promise.otype == .runnable then
      let due :=
        match promise.tags.get? "resonate:delay" with
        | some delay => max (parseNat delay) now
        | none => now
      let task : TaskObject :=
        { state := .pending, version := 0, retryTimeoutAt := some due }
      setTask suffix task
      return { suffix, promise, task := some task }
    return { suffix, promise }
  else
    let promiseState :=
      if tags.isTimer then PromiseState.resolved
      else PromiseState.rejectedTimedout
    let promise : PromiseObject :=
      { state := promiseState, param, tags, timeoutAt,
        createdAt := timeoutAt, settledAt := some timeoutAt }
    setPromise suffix promise
    if promise.otype == .runnable then
      let task : TaskObject := { state := .fulfilled, version := 0 }
      setTask suffix task
      return { suffix, promise, task := some task }
    return { suffix, promise }

def createPromise (req : PromiseCreateReq) (now : Nat) :
    Handler (.origin req.id.origin) (OriginObject req.id.origin) :=
  createPromiseAt req.id.suffix req.timeoutAt now req.param req.tags

/-- External reads project a view but do not persist it. -/
def readObject {origin : String} (suffix : String) (now : Nat) :
    Handler (.origin origin) (Option (OriginObject origin)) := do
  match ← getObject suffix with
  | none => return none
  | some object => return some (object.project now)

def readTaskObject {origin : String} (suffix : String) (now : Nat) :
    Handler (.origin origin) (Option (OriginObject origin)) := do
  match ← getObject suffix with
  | some object =>
      if object.task.isSome then readObject suffix now else return none
  | none => return none

def createIfAbsentAt {origin : String} (suffix : String) (timeoutAt now : Nat)
    (param : Value) (tags : Tags) : Handler (.origin origin) Unit := do
  match ← readObject suffix now with
  | some _ => pure ()
  | none =>
      let _ ← createPromiseAt suffix timeoutAt now param tags

def createIfAbsent (req : PromiseCreateReq) (now : Nat) :
    Handler (.origin req.id.origin) Unit :=
  createIfAbsentAt req.id.suffix req.timeoutAt now req.param req.tags

end Direct
end Resonate

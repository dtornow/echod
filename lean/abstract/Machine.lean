import «abstract».Protocol

/-!
# Document-scoped Resonate abstract machine

The global store is a dependent map. Promise/task rows are grouped by origin;
each schedule has a distinct document key and document type. A `Handler key`
receives only `Document key`, so neither bind nor any primitive can cross a
document boundary or inspect the global store.
-/

namespace Resonate

open ServerModel

namespace Direct

abbrev ServerConfig := AbstractModel.ServerConfig

abbrev Env := Resonate.HandlerEnv

/-- Fixed-key Reader+State+Writer. The state is exactly one document. -/
abbrev Handler := Resonate.DocumentHandler
abbrev ask := @Resonate.documentAsk
abbrev get := @Resonate.documentGet
abbrev set := @Resonate.documentSet
abbrev modify := @Resonate.documentModify
abbrev emit := @Resonate.documentEmit

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

def setMessage {key : DocumentKey} (address : String)
    (message : ServerModel.Message) :
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

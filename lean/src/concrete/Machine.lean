import «concrete».Document

/-!
# Concrete document decision machine

This is the concrete kernel's private Reader/State/Writer machine.  It is
intentionally independent of `Resonate.Abstract`: correspondence is proved only
in `refinement_proof`.
-/

namespace Resonate.Concrete.Decision

open ServerModel

abbrev Env := Resonate.HandlerEnv

abbrev Handler := Resonate.DocumentHandler
abbrev ask := @Resonate.documentAsk
abbrev get := @Resonate.documentGet
abbrev set := @Resonate.documentSet
abbrev modify := @Resonate.documentModify
abbrev emit := @Resonate.documentEmit

def run (config : Resonate.ServerConfig) (action : Handler key α)
    (document : Document key) : α × Document key × List OutboxEntry :=
  action { config } document

def getObject {origin : String} (suffix : String) :
    Handler (.origin origin) (Option (OriginObject origin)) := do
  return (← get).find? (·.suffix == suffix)

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
    (message : ServerModel.Message) : Handler key Unit :=
  emit { address, message }

/-- Settle a promise; a settled promise also finishes its task. -/
def setSettled {origin : String} (object : OriginObject origin)
    (promise : PromiseObject) : Handler (.origin origin) Unit :=
  setObject { object with promise, task := object.task.map (·.project promise) }

/-- A new promise, with a task if it is runnable. A promise created at or
past its deadline is created settled. -/
def newObject {origin : String} (suffix : String) (timeoutAt now : Nat)
    (param : Value) (tags : Tags) : OriginObject origin :=
  if timeoutAt > now then
    let promise : PromiseObject :=
      { state := .pending, param, tags, timeoutAt, createdAt := now }
    if promise.otype == .runnable then
      let due :=
        match promise.tags.get? "resonate:delay" with
        | some delay => max (parseNat delay) now
        | none => now
      { suffix, promise,
        task := some { state := .pending, version := 0, retryTimeoutAt := some due } }
    else { suffix, promise }
  else
    let state :=
      if tags.isTimer then PromiseState.resolved else PromiseState.rejectedTimedout
    let promise : PromiseObject :=
      { state, param, tags, timeoutAt,
        createdAt := timeoutAt, settledAt := some timeoutAt }
    if promise.otype == .runnable then
      { suffix, promise, task := some { state := .fulfilled, version := 0 } }
    else { suffix, promise }

def createPromiseAt {origin : String} (suffix : String) (timeoutAt now : Nat)
    (param : Value) (tags : Tags) :
    Handler (.origin origin) (OriginObject origin) := do
  let object := newObject suffix timeoutAt now param tags
  setObject object
  return object

def readObject {origin : String} (suffix : String) (now : Nat) :
    Handler (.origin origin) (Option (OriginObject origin)) := do
  match ← getObject suffix with
  | none => return none
  | some object => return some (object.project now)

def readTask {origin : String} (suffix : String) (now : Nat) :
    Handler (.origin origin) (Option (OriginObject origin × TaskObject)) := do
  match ← readObject suffix now with
  | some object => return object.task.map (object, ·)
  | none => return none

/-- The object at `req.id`, created from `req` if there is none. -/
def readOrCreate {origin : String} (req : PromiseCreateReq) (now : Nat) :
    Handler (.origin origin) (OriginObject origin) := do
  match ← readObject req.id.suffix now with
  | some object => return object
  | none => createPromiseAt req.id.suffix req.timeoutAt now req.param req.tags

end Resonate.Concrete.Decision

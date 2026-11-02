import Protocol

/-!
# Concrete document decision machine

This is the concrete kernel's private Reader/State/Writer machine.  It is
intentionally independent of `Resonate.Direct`: correspondence is proved only
in `concrete.refinement_proof`.
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
    (message : ServerModel.Message) : Handler key Unit :=
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

end Resonate.Concrete.Decision

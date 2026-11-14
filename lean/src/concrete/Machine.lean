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

def setSchedule {id : Ident} (schedule : Schedule) :
    Handler (.schedule id) Unit :=
  set (some {
    cron := schedule.cron
    promiseId := schedule.promiseId
    promiseTimeout := schedule.promiseTimeout
    promiseParam := schedule.promiseParam
    promiseTags := schedule.promiseTags
    nextRunAt := schedule.nextRunAt
    lastRunAt := schedule.lastRunAt
    createdAt := schedule.createdAt })

def delSchedule {id : Ident} : Handler (.schedule id) Unit :=
  set none

def setMessage {key : DocumentKey} (address : String)
    (message : ServerModel.Message) : Handler key Unit :=
  emit { address, message }

/-- Emit the current task offer and arm its next retry in the same write. -/
def dispatchTask {origin : String} (object : OriginObject origin)
    (task : TaskObject) (now : Nat) : Handler (.origin origin) Unit := do
  let env ← ask
  let next := { task with
    retryTimeoutAt := some (now + env.config.retryTimeout) }
  setObject { object with task := some next }
  setMessage
    ((object.promise.tags.get? "resonate:target").getD "")
    (.execute object.id task.version)

/-- Dispatch a runnable task exactly when its retry clock is due. -/
def dispatchIfDue {origin : String} (object : OriginObject origin) (now : Nat) :
    Handler (.origin origin) Unit := do
  match object.task with
  | some task =>
      if task.state == .pending ∧ task.retryTimeoutAt.any (· ≤ now) then
        dispatchTask object task now
  | none => pure ()

/-- A new promise, with a task if it is runnable. A promise created at or
past its deadline is created settled. -/
def newObject {origin : String} (suffix : String) (timeoutAt now : Nat)
    (param : Value) (tags : Tags) : OriginObject origin :=
  if timeoutAt > now then
    let promise : PromiseObject :=
      { state := .pending, param, tags, timeoutAt, createdAt := now }
    if promise.otype == .runnable then
      { suffix, promise,
        task := some { state := .pending, version := 0, retryTimeoutAt := some now } }
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

/-- Resume one awaiter. Suspended work is offered immediately; work that is
already queued or running only records the resume. -/
def resumeOne (awaited awaiter : Ident) (now : Nat) :
    Handler (.origin awaited.origin) Unit := do
  if !awaited.sameOrigin awaiter then return ()
  match ← readTask awaiter.suffix now with
  | none => pure ()
  | some (object, task) =>
      match task.state with
      | .suspended =>
          dispatchTask object
            { task with
              state := .pending
              pid := none
              ttl := none
              leaseTimeoutAt := none
              resumes := [awaited] }
            now
      | .pending | .acquired | .halted =>
          if !(task.resumes.contains awaited) then
            setObject { object with
              task := some { task with resumes := task.resumes ++ [awaited] } }
      | .fulfilled => pure ()

def resumeAll (awaited : Ident) (now : Nat) :
    List Ident → Handler (.origin awaited.origin) Unit
  | [] => pure ()
  | awaiter :: rest => do
      resumeOne awaited awaiter now
      resumeAll awaited now rest

def notifyAll {origin : String} (promise : PromiseObject) (id : Ident) :
    List String → Handler (.origin origin) Unit
  | [] => pure ()
  | address :: rest => do
      setMessage address (.unblock (promise.toRecord id))
      notifyAll promise id rest

/-- Settlement is one document transition: store the settled row, synchronously
drain every callback and listener, and include their effects in this handler. -/
def setSettled {origin : String} (object : OriginObject origin)
    (promise : PromiseObject) (now : Nat) : Handler (.origin origin) Unit := do
  let settled := { promise with callbacks := [], listeners := [] }
  setObject { object with
    promise := settled
    task := object.task.map (·.project settled) }
  resumeAll object.id now promise.callbacks
  notifyAll settled object.id promise.listeners

/-- The object at `req.id`, created from `req` if there is none. -/
def readOrCreate {origin : String} (req : PromiseCreateReq) (now : Nat) :
    Handler (.origin origin) (OriginObject origin) := do
  match ← readObject req.id.suffix now with
  | some object => return object
  | none => createPromiseAt req.id.suffix req.timeoutAt now req.param req.tags

end Resonate.Concrete.Decision

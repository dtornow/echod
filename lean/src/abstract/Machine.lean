import Protocol

/-!
# Abstract Resonate machine

The store is a list of objects (a promise and its task, by id) and a list of
schedules. A handler reads the objects it names by id and writes back the
ones it changes. Every read is by id, so the order of the lists carries no
meaning.
-/

namespace Resonate

open ServerModel

/-- The object as it reads at `now`: a pending promise past its deadline is
settled at the deadline, and the task of a settled promise is fulfilled. -/
def Object.project (object : Object) (now : Nat) : Object :=
  let p := object.promise
  let promise :=
    if p.state == .pending ∧ p.timeoutAt ≤ now then
      if p.isTimer then { p with state := .resolved, settledAt := some p.timeoutAt }
      else { p with state := .rejectedTimedout, settledAt := some p.timeoutAt }
    else p
  let task := object.task.map fun t =>
    if promise.state != .pending ∧ t.state != .fulfilled then t.fulfill else t
  { object with promise, task }

/-- The task taken by `pid` for `ttl`, from `now`. -/
def _root_.AbstractModel.TaskObject.acquire (t : TaskObject) (pid : String) (ttl now : Nat) :
    TaskObject :=
  { t with
    state := .acquired, version := t.version + 1, ttl := some ttl, pid := some pid,
    leaseTimeoutAt := some (now + ttl), retryTimeoutAt := none, resumes := [] }

/-- The task in `state` with no lease, retried at `retry`. -/
def _root_.AbstractModel.TaskObject.unlease (t : TaskObject) (state : TaskState)
    (retry : Option Nat) : TaskObject :=
  { t with state, pid := none, ttl := none, leaseTimeoutAt := none, retryTimeoutAt := retry }

def Store.getObject (store : Store) (id : Ident) : Option Object :=
  store.objects.find? (·.id == id)

/-- Write an object, replacing the one with its id. -/
def Store.setObject (store : Store) (object : Object) : Store :=
  { store with objects := object :: store.objects.filter (·.id != object.id) }

def Store.getSchedule (store : Store) (id : Ident) : Option Schedule :=
  store.schedules.find? (·.id == id)

/-- Write a schedule, replacing the one with its id. -/
def Store.setSchedule (store : Store) (schedule : Schedule) : Store :=
  { store with
    schedules := schedule :: store.schedules.filter (·.id != schedule.id) }

def Store.deleteSchedule (store : Store) (id : Ident) : Store :=
  { store with schedules := store.schedules.filter (·.id != id) }

namespace Abstract

abbrev Env := Resonate.HandlerEnv

/-- Read the configuration, read and write the store, emit messages.
A read sees the writes made earlier in the same step. -/
abbrev Handler (α : Type) :=
  HandlerEnv → Store → α × Store × List OutboxEntry

instance : Monad Handler where
  pure value := fun _ store => (value, store, [])
  bind action next := fun env store =>
    let (value, store', emitted₁) := action env store
    let (result, store'', emitted₂) := next value env store'
    (result, store'', emitted₁ ++ emitted₂)

def ask : Handler Env := fun env store => (env, store, [])

def getStore : Handler Store := fun _ store => (store, store, [])

def getObject (id : Ident) : Handler (Option Object) := fun _ store =>
  (store.getObject id, store, [])

def setObject (object : Object) : Handler Unit :=
  fun _ store => ((), store.setObject object, [])

def getSchedule (id : Ident) : Handler (Option Schedule) := fun _ store =>
  (store.getSchedule id, store, [])

def setSchedule (schedule : Schedule) : Handler Unit :=
  fun _ store => ((), store.setSchedule schedule, [])

def deleteSchedule (id : Ident) : Handler Unit :=
  fun _ store => ((), store.deleteSchedule id, [])

def setMessage (address : String) (message : ServerModel.Message) : Handler Unit :=
  fun _ store => ((), store, [{ address, message }])

/-- Read one object as seen at `now`. -/
def readObject (id : Ident) (now : Nat) : Handler (Option Object) := do
  return (← getObject id).map (·.project now)

/-- Read one object together with its task. -/
def readTask (id : Ident) (now : Nat) : Handler (Option (Object × TaskObject)) := do
  match ← readObject id now with
  | some object => return object.task.map (object, ·)
  | none => return none

/-- Emit the current task offer and arm its next retry in the same write. -/
def dispatchTask (object : Object) (task : TaskObject) (now : Nat) : Handler Unit := do
  let env ← ask
  let next := { task with
    retryTimeoutAt := some (now + env.config.retryTimeout) }
  setObject { object with task := some next }
  setMessage
    ((object.promise.tags.get? "resonate:target").getD "")
    (.execute object.id task.version)

/-- Dispatch a runnable task exactly when its retry clock is due. -/
def dispatchIfDue (object : Object) (now : Nat) : Handler Unit := do
  match object.task with
  | some task =>
      if task.state == .pending ∧ task.retryTimeoutAt.any (· ≤ now) then
        dispatchTask object task now
  | none => pure ()

/-- Resume one awaiter. Suspended work is offered immediately; work that is
already queued or running only records the resume. -/
def resumeOne (awaited awaiter : Ident) (now : Nat) : Handler Unit := do
  if !awaited.sameOrigin awaiter then return ()
  match ← readTask awaiter now with
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

def resumeAll (awaited : Ident) (now : Nat) : List Ident → Handler Unit
  | [] => pure ()
  | awaiter :: rest => do
      resumeOne awaited awaiter now
      resumeAll awaited now rest

def notifyAll (promise : PromiseObject) (id : Ident) : List String → Handler Unit
  | [] => pure ()
  | address :: rest => do
      setMessage address (.unblock (promise.toRecord id))
      notifyAll promise id rest

/-- Settlement is one document transition: store the settled row, synchronously
drain every callback and listener, and include their effects in this handler. -/
def setSettled (object : Object) (promise : PromiseObject) (now : Nat) : Handler Unit := do
  let settled := { promise with callbacks := [], listeners := [] }
  setObject ({ object with promise := settled }.project now)
  resumeAll object.id now promise.callbacks
  notifyAll settled object.id promise.listeners

/-- A new promise, with a task if it is runnable. A promise created at or
past its deadline is created settled. -/
def newObject (id : Ident) (timeoutAt now : Nat) (param : Value) (tags : Tags) :
    Object :=
  if timeoutAt > now then
    let promise : PromiseObject :=
      { state := .pending, param, tags, timeoutAt, createdAt := now }
    if promise.otype == .runnable then
      { id, promise,
        task := some { state := .pending, version := 0, retryTimeoutAt := some now } }
    else { id, promise }
  else
    let state :=
      if tags.isTimer then PromiseState.resolved else PromiseState.rejectedTimedout
    let promise : PromiseObject :=
      { state, param, tags, timeoutAt,
        createdAt := timeoutAt, settledAt := some timeoutAt }
    if promise.otype == .runnable then
      { id, promise, task := some { state := .fulfilled, version := 0 } }
    else { id, promise }

def createPromiseAt (id : Ident) (timeoutAt now : Nat) (param : Value)
    (tags : Tags) : Handler Object := do
  let object := newObject id timeoutAt now param tags
  setObject object
  return object

/-- The object at `req.id`, created from `req` if there is none. -/
def readOrCreate (req : PromiseCreateReq) (now : Nat) : Handler Object := do
  match ← readObject req.id now with
  | some o => return o
  | none => createPromiseAt req.id req.timeoutAt now req.param req.tags

def createIfAbsent (req : PromiseCreateReq) (now : Nat) : Handler Unit := do
  let _ ← readOrCreate req now

end Abstract
end Resonate

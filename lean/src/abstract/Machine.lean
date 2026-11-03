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

/-- Settle a promise; a settled promise also finishes its task. -/
def setSettled (object : Object) (promise : PromiseObject) (now : Nat) : Handler Unit :=
  setObject ({ object with promise }.project now)

/-- A new promise, with a task if it is runnable. A promise created at or
past its deadline is created settled. -/
def newObject (id : Ident) (timeoutAt now : Nat) (param : Value) (tags : Tags) :
    Object :=
  if timeoutAt > now then
    let promise : PromiseObject :=
      { state := .pending, param, tags, timeoutAt, createdAt := now }
    if promise.otype == .runnable then
      let due :=
        match promise.tags.get? "resonate:delay" with
        | some delay => max (parseNat delay) now
        | none => now
      { id, promise,
        task := some { state := .pending, version := 0, retryTimeoutAt := some due } }
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

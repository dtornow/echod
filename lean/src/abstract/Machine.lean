import Protocol

/-!
# Abstract Resonate machine

The store is a list of objects (a promise and its task, by id) and a list of
schedules. A handler reads the objects it names by id and writes back the
ones it changes.
-/

namespace Resonate

open ServerModel

def Object.project (object : Object) (now : Nat) : Object :=
  let promise := object.promise.project now
  { object with promise, task := object.task.map (·.view promise) }

def Store.getObject (store : Store) (id : Ident) : Option Object :=
  store.objects.find? (·.id == id)

/-- Write the promise of `id`, creating the object if it is new. -/
def Store.setPromise (store : Store) (id : Ident) (promise : PromiseObject) :
    Store :=
  let object : Object :=
    match store.getObject id with
    | some existing => { existing with promise }
    | none => { id, promise }
  { store with objects := object :: store.objects.filter (·.id != id) }

def Store.setTask (store : Store) (id : Ident) (task : TaskObject) : Store :=
  { store with
    objects := store.objects.map fun object =>
      if object.id == id then { object with task := some task } else object }

def Store.setObject (store : Store) (object : Object) : Store :=
  { store with objects := object :: store.objects.filter (·.id != object.id) }

def Store.getSchedule (store : Store) (id : Ident) : Option Schedule :=
  store.schedules.find? (·.id == id)

def Store.setSchedule (store : Store) (schedule : Schedule) : Store :=
  { store with
    schedules := store.schedules.filter (·.id != schedule.id) ++ [schedule] }

def Store.deleteSchedule (store : Store) (id : Ident) : Store :=
  { store with schedules := store.schedules.filter (·.id != id) }

namespace Abstract

abbrev ServerConfig := AbstractModel.ServerConfig

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

def setPromise (id : Ident) (promise : PromiseObject) : Handler Unit :=
  fun _ store => ((), store.setPromise id promise, [])

def setTask (id : Ident) (task : TaskObject) : Handler Unit :=
  fun _ store => ((), store.setTask id task, [])

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

/-- Read one object that has a task. -/
def readTaskObject (id : Ident) (now : Nat) : Handler (Option Object) := do
  match ← readObject id now with
  | some object => if object.task.isSome then return some object else return none
  | none => return none

/-- Settle a promise; a settled promise also finishes its task. -/
def setSettled (id : Ident) (object : Object) (promise : PromiseObject) :
    Handler Unit := do
  setPromise id promise
  if promise.state != .pending then
    match object.task with
    | some task => if task.state != .fulfilled then setTask id task.fulfill
    | none => pure ()

def createPromiseAt (id : Ident) (timeoutAt now : Nat) (param : Value)
    (tags : Tags) : Handler Object := do
  if timeoutAt > now then
    let promise : PromiseObject :=
      { state := .pending, param, tags, timeoutAt, createdAt := now }
    setPromise id promise
    if promise.otype == .runnable then
      let due :=
        match promise.tags.get? "resonate:delay" with
        | some delay => max (parseNat delay) now
        | none => now
      let task : TaskObject :=
        { state := .pending, version := 0, retryTimeoutAt := some due }
      setTask id task
      return { id, promise, task := some task }
    return { id, promise }
  else
    let state :=
      if tags.isTimer then PromiseState.resolved else PromiseState.rejectedTimedout
    let promise : PromiseObject :=
      { state, param, tags, timeoutAt,
        createdAt := timeoutAt, settledAt := some timeoutAt }
    setPromise id promise
    if promise.otype == .runnable then
      let task : TaskObject := { state := .fulfilled, version := 0 }
      setTask id task
      return { id, promise, task := some task }
    return { id, promise }

def createIfAbsent (req : PromiseCreateReq) (now : Nat) : Handler Unit := do
  if (← readObject req.id now).isNone then
    let _ ← createPromiseAt req.id req.timeoutAt now req.param req.tags

end Abstract
end Resonate

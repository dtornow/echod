import «02-abstract».«system»

/-!
# Direct-state Resonate abstract machine

This module uses the public protocol and fused object representation from the
pinned `resonatehq/resonate` specification.  Unlike that specification's
effect-list interpreter, `H` is an ordinary Reader+State monad: every write is
applied immediately and later reads in the same handler observe it.
-/

namespace Resonate.Direct

open ServerModel

abbrev PromiseObject := AbstractModel.PromiseObject
abbrev TaskObject := AbstractModel.TaskObject
abbrev Object := AbstractModel.Object
abbrev ServerState := AbstractModel.ServerState
abbrev ServerConfig := AbstractModel.ServerConfig

deriving instance DecidableEq for Value
deriving instance DecidableEq for PromiseRecord
deriving instance DecidableEq for TaskRecord
deriving instance DecidableEq for Schedule
deriving instance DecidableEq for Message
deriving instance DecidableEq for OutboxEntry

structure Env where
  config : ServerConfig := {}

/-- A small Reader+State monad.  Bind threads the updated state. -/
def H (α : Type) : Type := Env → ServerState → α × ServerState

instance : Monad H where
  pure a := fun _ s => (a, s)
  bind x f := fun e s =>
    let (a, s') := x e s
    f a e s'

def ask : H Env := fun e s => (e, s)
def get : H ServerState := fun _ s => (s, s)
def set (s : ServerState) : H Unit := fun _ _ => ((), s)
def modify (f : ServerState → ServerState) : H Unit :=
  fun _ s => ((), f s)

def runWith (config : ServerConfig) (act : H α) (state : ServerState) :
    α × ServerState :=
  act { config } state

def run (act : H α) (state : ServerState) : α × ServerState :=
  runWith {} act state

def getObject (id : Ident) : H (Option Object) := do
  return (← get).objects.find? (·.id == id)

def getSchedule (id : Ident) : H (Option Schedule) := do
  return (← get).schedules.find? (·.id == id)

def setPromise (id : Ident) (p : PromiseObject) : H Unit :=
  modify fun s =>
    { s with
      objects :=
        AbstractModel.Object.withPromise id p
            (s.objects.find? (·.id == id))
          :: s.objects.filter (·.id != id) }

def setTask (id : Ident) (t : TaskObject) : H Unit :=
  modify fun s =>
    { s with
      objects := s.objects.map fun o =>
        if o.id == id then { o with task := some t } else o }

def setSchedule (schedule : Schedule) : H Unit :=
  modify fun s =>
    { s with
      schedules := schedule :: s.schedules.filter (·.id != schedule.id) }

def delSchedule (id : Ident) : H Unit :=
  modify fun s =>
    { s with schedules := s.schedules.filter (·.id != id) }

def setMessage (address : String) (message : Message) : H Unit :=
  modify fun s =>
    let entry : OutboxEntry := { address, message }
    { s with
      outbox := entry :: s.outbox.filter (fun old => old.key != entry.key) }

def setSettled (o : Object) (p : PromiseObject) : H Unit := do
  setPromise o.id p
  if p.state != .pending then
    match o.task with
    | some t =>
        if t.state != .fulfilled then setTask o.id t.fulfill
    | none => pure ()

def createPromise (req : PromiseCreateReq) (now : Nat) : H Object := do
  if req.timeoutAt > now then
    let p : PromiseObject :=
      { state := .pending, param := req.param, tags := req.tags,
        timeoutAt := req.timeoutAt, createdAt := now }
    setPromise req.id p
    if p.otype == .runnable then
      let due :=
        match p.tags.get? "resonate:delay" with
        | some delay => max (parseNat delay) now
        | none => now
      let t : TaskObject :=
        { state := .pending, version := 0, retryTimeoutAt := some due }
      setTask req.id t
      return { id := req.id, promise := p, task := some t }
    return { id := req.id, promise := p }
  else
    let promiseState :=
      if req.tags.isTimer then PromiseState.resolved
      else PromiseState.rejectedTimedout
    let p : PromiseObject :=
      { state := promiseState, param := req.param, tags := req.tags,
        timeoutAt := req.timeoutAt, createdAt := req.timeoutAt,
        settledAt := some req.timeoutAt }
    setPromise req.id p
    if p.otype == .runnable then
      let t : TaskObject := { state := .fulfilled, version := 0 }
      setTask req.id t
      return { id := req.id, promise := p, task := some t }
    return { id := req.id, promise := p }

/-- Read and project without persisting. This is the less restrictive
external-read discipline: handlers observe timeout/task projection while the
stored row remains unchanged unless the handler explicitly writes it. -/
def readObject (id : Ident) (now : Nat) : H (Option Object) := do
  match ← getObject id with
  | none => return none
  | some object => return some (object.project now)

def readTaskObject (id : Ident) (now : Nat) : H (Option Object) := do
  match ← getObject id with
  | some o =>
      if o.task.isSome then readObject id now else return none
  | none => return none

def materialise (id : Ident) (before after : Object) : H Unit := do
  if after.promise.state != before.promise.state then
    setPromise id after.promise
  match before.task, after.task with
  | some old, some new =>
      if new.state != old.state then setTask id new
  | _, _ => pure ()

/-- Internal work takes the forced read and persists projection. -/
def touchObject (id : Ident) (now : Nat) : H (Option Object) := do
  match ← getObject id with
  | none => return none
  | some before =>
      let after := before.project now
      materialise id before after
      return some after

abbrev viewObject := readObject

def touchTaskObject (id : Ident) (now : Nat) : H (Option Object) := do
  match ← getObject id with
  | some object =>
      if object.task.isSome then touchObject id now else return none
  | none => return none

abbrev viewTaskObject := readTaskObject

def createIfAbsent (req : PromiseCreateReq) (now : Nat) : H Unit := do
  match ← readObject req.id now with
  | some _ => pure ()
  | none =>
      let _ ← createPromise req now

end Resonate.Direct

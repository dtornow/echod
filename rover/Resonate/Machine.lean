import «02-abstract».«system»

/-!
# Direct-state Resonate abstract machine

This module uses the public protocol and fused object representation from the
pinned `resonatehq/resonate` specification. Unlike that specification's
effect-list interpreter, `H` is an ordinary Reader+State+Writer monad: every
state write is applied immediately, later reads in the same handler observe it,
and boundary messages are accumulated in emission order.
-/

namespace Resonate

open ServerModel

abbrev PromiseObject := AbstractModel.PromiseObject
abbrev TaskObject := AbstractModel.TaskObject
abbrev Object := AbstractModel.Object

/-- Rover's abstract Resonate state. Boundary emissions are transient Writer
output and are deliberately not durable server state. -/
structure State where
  objects : List Object := []
  schedules : List Schedule := []
  deriving Repr

def State.init : State := {}

namespace Direct

abbrev ServerConfig := AbstractModel.ServerConfig

deriving instance DecidableEq for Value
deriving instance DecidableEq for PromiseRecord
deriving instance DecidableEq for TaskRecord
deriving instance DecidableEq for Schedule
deriving instance DecidableEq for Message
deriving instance DecidableEq for OutboxEntry

structure Env where
  config : ServerConfig := {}

/-- A small Reader+State+Writer monad. Bind threads updated state and appends
emissions in program order. -/
def H (α : Type) : Type :=
  Env → State → α × State × List OutboxEntry

instance : Monad H where
  pure a := fun _ s => (a, s, [])
  bind x f := fun e s =>
    let (a, s', emitted₁) := x e s
    let (b, s'', emitted₂) := f a e s'
    (b, s'', emitted₁ ++ emitted₂)

def ask : H Env := fun e s => (e, s, [])
def get : H State := fun _ s => (s, s, [])
def set (s : State) : H Unit := fun _ _ => ((), s, [])
def modify (f : State → State) : H Unit :=
  fun _ s => ((), f s, [])
def emit (entry : OutboxEntry) : H Unit :=
  fun _ s => ((), s, [entry])

def runWith (config : ServerConfig) (act : H α) (state : State) :
    α × State × List OutboxEntry :=
  act { config } state

def run (act : H α) (state : State) : α × State × List OutboxEntry :=
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
  emit { address, message }

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

/-- The single object read operation. It returns the object's projected view
without persisting that projection, following the permissive abstract read
discipline. -/
def readObject (id : Ident) (now : Nat) : H (Option Object) := do
  match ← getObject id with
  | none => return none
  | some object => return some (object.project now)

def readTaskObject (id : Ident) (now : Nat) : H (Option Object) := do
  match ← getObject id with
  | some o =>
      if o.task.isSome then readObject id now else return none
  | none => return none

def createIfAbsent (req : PromiseCreateReq) (now : Nat) : H Unit := do
  match ← readObject req.id now with
  | some _ => pure ()
  | none =>
      let _ ← createPromise req now

end Direct
end Resonate

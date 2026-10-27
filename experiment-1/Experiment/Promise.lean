import Experiment.Service

/-!
# Promises, written as handlers

A slice of Resonate's promise protocol (get, create, settle, listen, and
timeouts) written in the handler monad. It follows the specification's
handlers where it overlaps with them, with one simplification: a listener
is told the moment a promise settles, by the step that settles it, rather
than by a later internal step.

**Everything that leaves is a message.** A response is a message to the
requester; a notification is a message to a listener. Both go out through
the same `send`.

**Where the specification allows a choice, the handler chooses**: with
`mayShed`, any request may be answered 503 and do nothing.

**The top level is Kleppmann's step function**: the server receives a
message from a sender at `now` and sends messages. A request is dispatched,
by a `match`, to its handler; the handler's response is sent back to the
sender.
-/

namespace Experiment

abbrev Ident := String
abbrev CallId := Nat

inductive PromiseState where
  | pending
  | resolved
  | rejected
  | rejectedCanceled
  | rejectedTimedout
  deriving DecidableEq, Repr

/-- What a client may settle a promise to. -/
def PromiseState.settable : PromiseState → Bool
  | .resolved | .rejected | .rejectedCanceled => true
  | _ => false

structure Promise where
  id        : Ident
  state     : PromiseState := .pending
  value     : String := ""
  timeoutAt : Time
  listeners : List Addr := []
  deriving DecidableEq, Repr

/-- A promise as clients see it: no listeners. -/
structure Record where
  id        : Ident
  state     : PromiseState
  value     : String
  timeoutAt : Time
  deriving DecidableEq, Repr

def Promise.record (p : Promise) : Record := ⟨p.id, p.state, p.value, p.timeoutAt⟩

/-! ## Environment, state, messages, signals -/

structure Config where
  /-- The timeout of a promise created without one, from its creation. -/
  defaultTimeout : Time := 1000
  /-- Whether the server may shed load: answer 503 to any request, and do
      nothing. A choice the specification allows, not a fault. -/
  mayShed : Bool := false
  deriving Repr

structure State where
  promises : List Promise := []
  deriving DecidableEq, Repr

inductive Request where
  | get    (id : Ident)
  | create (id : Ident) (timeoutAt : Option Time)
  | settle (id : Ident) (state : PromiseState) (value : String)
  | listen (id : Ident) (address : Addr)
  deriving DecidableEq, Repr

structure Response where
  status  : Nat
  promise : Option Record := none
  deriving DecidableEq, Repr

inductive Msg where
  | req    (id : CallId) (r : Request)
  | res    (id : CallId) (r : Response)
  | notify (p : Record)
  deriving DecidableEq, Repr

abbrev Handler := H Config State (Out Msg)

def send (to : Addr) (m : Msg) : Handler Unit := emit (.send to m)
def always (name : String) (ok : Bool) : Handler Unit := emit (.always name ok)
def sometimes (name : String) (hit : Bool) : Handler Unit := emit (.sometimes name hit)

/-! ## Helpers -/

def save (p : Promise) : Handler Unit :=
  modify fun s => { s with promises := p :: s.promises.filter (·.id != p.id) }

/-- Settle a pending promise, and tell everyone listening. -/
def settle (p : Promise) (state : PromiseState) (value : String) : Handler Promise := do
  always "only a pending promise settles" (p.state == .pending)
  always "a promise settles to a final state" (state != .pending)
  let p' := { p with state, value, listeners := [] }
  save p'
  for a in p.listeners do
    send a (.notify p'.record)
  return p'

/-- Read a promise at `now`. A promise past its timeout times out here, so
    every read sees it timed out, and its listeners hear of it once. -/
def load (id : Ident) (now : Time) : Handler (Option Promise) := do
  match (← get).promises.find? (·.id == id) with
  | none => return none
  | some p =>
    if p.state == .pending && p.timeoutAt ≤ now then
      return some (← settle p .rejectedTimedout "")
    else
      return some p

def ok (p : Promise) : Response := { status := 200, promise := some p.record }

/-! ## The handlers -/

def promiseGet (id : Ident) (now : Time) : Handler Response := do
  match ← load id now with
  | none => return { status := 404 }
  | some p => return ok p

def promiseCreate (id : Ident) (timeoutAt : Option Time) (now : Time) : Handler Response := do
  match ← load id now with
  | some p =>
    sometimes "create finds the promise settled" (p.state != .pending)
    return ok p
  | none =>
    let timeoutAt := timeoutAt.getD (now + (← read).defaultTimeout)
    let p : Promise :=
      { id, timeoutAt, state := if timeoutAt ≤ now then .rejectedTimedout else .pending }
    save p
    return ok p

def promiseSettle (id : Ident) (state : PromiseState) (value : String) (now : Time) :
    Handler Response := do
  if !state.settable then return { status := 400 }
  match ← load id now with
  | none => return { status := 404 }
  | some p =>
    if p.state == .pending then
      return ok (← settle p state value)
    else
      sometimes "settle arrives after the timeout" (p.state == .rejectedTimedout)
      return ok p

def promiseListen (id : Ident) (address : Addr) (now : Time) : Handler Response := do
  match ← load id now with
  | none => return { status := 404 }
  | some p =>
    if p.state == .pending && !p.listeners.contains address then
      let p := { p with listeners := p.listeners ++ [address] }
      save p
      return ok p
    else
      return ok p

/-! ## The top level -/

/-- A request, dispatched to its handler; unless the server sheds it. -/
def request (r : Request) (now : Time) : Handler Response := do
  if (← read).mayShed then
    if ← choose ⟨[false, true], by simp⟩ then return { status := 503 }
  match r with
  | .get id            => promiseGet id now
  | .create id t       => promiseCreate id t now
  | .settle id st v    => promiseSettle id st v now
  | .listen id address => promiseListen id address now

/-- The server's step on a message: a request is answered with a message
    back to its sender. The server receives nothing else. -/
def receive (sender : Addr) (m : Msg) (now : Time) : Handler Unit :=
  match m with
  | .req id r => do send sender (.res id (← request r now))
  | _ => pure ()

/-- The server's step on a tick: every promise past its timeout times out. -/
def timeout (now : Time) : Handler Unit := do
  for p in (← get).promises do
    let _ ← load p.id now

/-- The promise service: what every shell runs. -/
abbrev promises : Service where
  Config  := Config
  State   := State
  Msg     := Msg
  receive := receive
  tick    := timeout

end Experiment

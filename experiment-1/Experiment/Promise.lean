import Experiment.Handler

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

**The top level is Kleppmann's step function**: the server receives a
message from a sender at `now` and sends messages. A request is dispatched,
by a `match`, to its handler; the handler's response is sent back to the
sender.
-/

namespace Experiment

abbrev Time := Nat
abbrev Addr := String
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

/-- What a handler emits: a message to send, or an assertion. -/
inductive Out where
  | send      (to : Addr) (m : Msg)
  /-- Must hold every time it is emitted. -/
  | always    (name : String) (ok : Bool)
  /-- Should hold at least once, over a fuzzing run. -/
  | sometimes (name : String) (hit : Bool)
  deriving DecidableEq, Repr

abbrev Handler := H Config State Out

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

/-- A request, dispatched to its handler. -/
def request (r : Request) (now : Time) : Handler Response :=
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

/-! ## Running it -/

/-- What the server sent, and what it asserted. -/
def sent (outs : List Out) : List (Addr × Msg) :=
  outs.filterMap fun | .send a m => some (a, m) | _ => none

def failed (outs : List Out) : List String :=
  outs.filterMap fun | .always n false => some n | _ => none

def hit (outs : List Out) : List String :=
  outs.filterMap fun | .sometimes n true => some n | _ => none

/-- One input to the server: a request from a client, or a tick. -/
inductive Input where
  | call (from_ : Addr) (id : CallId) (r : Request)
  | tick

/-- Run inputs at their instants; everything the server emitted, in order. -/
def simulate (cfg : Config) (inputs : List (Time × Input)) : State × List Out :=
  inputs.foldl (fun (s, outs) (now, i) =>
    let step := match i with
      | .call a id r => receive a (.req id r) now
      | .tick => timeout now
    let ((), s', outs') := step.run cfg s
    (s', outs ++ outs')) ({}, [])

/-! ## A scenario

`c` creates `p` with a timeout at 10; `w` listens; `c` reads at 5 and at
20; `c` tries to settle at 21. -/

def scenario : List (Time × Input) :=
  [ (0,  .call "c" 1 (.create "p" (some 10))),
    (1,  .call "w" 2 (.listen "p" "w")),
    (5,  .call "c" 3 (.get "p")),
    (20, .call "c" 4 (.get "p")),
    (21, .call "c" 5 (.settle "p" .resolved "v")) ]

def timedOut : Record := ⟨"p", .rejectedTimedout, "", 10⟩

#guard (sent (simulate {} scenario).2).map (·.1) == ["c", "w", "c", "w", "c", "c"]
-- The read at 20 times the promise out: `w` is told, then `c` answered.
#guard (sent (simulate {} scenario).2)[3]? == some ("w", .notify timedOut)
#guard (sent (simulate {} scenario).2)[4]? == some ("c", .res 4 ⟨200, some timedOut⟩)
-- The late settle sees the timeout, and the assertion that wants that is hit.
#guard (sent (simulate {} scenario).2)[5]? == some ("c", .res 5 ⟨200, some timedOut⟩)
#guard hit (simulate {} scenario).2 == ["settle arrives after the timeout"]
#guard failed (simulate {} scenario).2 == []

-- Without a read, a tick at 20 does it: `w` is told once, at the tick.
#guard sent (simulate {} [(0, .call "c" 1 (.create "p" (some 10))), (1, .call "w" 2 (.listen "p" "w")),
    (20, .tick), (30, .tick)]).2 ==
  [("c", .res 1 ⟨200, some ⟨"p", .pending, "", 10⟩⟩), ("w", .res 2 ⟨200, some ⟨"p", .pending, "", 10⟩⟩),
   ("w", .notify timedOut)]

-- The default timeout comes from the configuration.
#guard (sent (simulate {} [(0, .call "c" 1 (.create "p" none))]).2) ==
  [("c", .res 1 ⟨200, some ⟨"p", .pending, "", 1000⟩⟩)]
#guard (sent (simulate { defaultTimeout := 5 } [(0, .call "c" 1 (.create "p" none))]).2) ==
  [("c", .res 1 ⟨200, some ⟨"p", .pending, "", 5⟩⟩)]

/-! ## A small fuzzer

Every sequence of three requests from a handful, at instants 0, 5 and 20:
no `always` fails, and every `sometimes` is hit somewhere. -/

def alphabet : List Request :=
  [.create "p" (some 10), .create "p" none, .get "p", .settle "p" .resolved "v",
   .settle "p" .pending "", .listen "p" "w"]

def runs : List (List Out) :=
  alphabet.flatMap fun a => alphabet.flatMap fun b => alphabet.map fun c =>
    (simulate {} [(0, .call "c" 1 a), (5, .call "c" 2 b), (20, .call "c" 3 c)]).2

#guard runs.length == 216
#guard runs.all (failed · == [])
#guard ["create finds the promise settled", "settle arrives after the timeout"].all
  fun n => runs.any fun o => (hit o).contains n

end Experiment

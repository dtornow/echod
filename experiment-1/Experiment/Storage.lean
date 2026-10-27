import Experiment.Promise
import Experiment.Network
import Experiment.Check

/-!
# The promise service on object storage

A simplified echod. Nodes keep nothing durable: every promise is a
document in a store, under its id, at a version. To serve a request a node
loads the request's document, runs the **abstract handler** on it, and
writes the result back conditionally on the version it loaded. If the
write loses a race it loads again and decides again. It answers and sends
the step's notifications only after the write lands, and it answers 503 if
the store does not say whether the write landed.

The store is a process too: a map from key to document and version,
conditional writes, and, when flaky, a failure that may or may not have
happened: a `choose`.

Simplifications against echod: one promise per document (echod: one
origin per document, as JSON lines), no cache, no deadline keys and no
sweeps (a timeout is seen when a request loads the document, as in the
abstract handlers), no membership (a client picks any node).

**Refinement, checked per run.** What the clients saw, requests and
answers with their times, is checked against the abstract service in the
abstract world of `Concurrent.lean` (`Check.lean`): the search finds where
each request took effect.
-/

namespace Experiment.Storage

open Experiment (Service Out sends emit choose H Some Time Addr Ident CallId Promise Request
  Response Msg pick lcg)

abbrev Version := Nat
abbrev OpId := Nat

/-- What travels: the protocol between clients and nodes, unchanged, and
    the store's calls and answers. -/
inductive CMsg where
  | app (m : Msg)
  | get (op : OpId) (key : Ident)
  /-- Write `p` at `key`, if the version there is `ifMatch` (`none`: if absent). -/
  | put (op : OpId) (key : Ident) (p : Promise) (ifMatch : Option Version)
  | got (op : OpId) (doc : Option (Promise × Version))
  | written (op : OpId)
  | conflict (op : OpId)
  /-- The write may or may not have landed. -/
  | failed (op : OpId)
  deriving DecidableEq, Repr

structure Config where
  store       : Addr := "s3"
  /-- Whether writes are conditional. Turn off to see what goes wrong. -/
  conditional : Bool := true
  /-- Whether a write may fail, landed or not. -/
  flaky       : Bool := false
  /-- How many lost races a request survives. -/
  retries     : Nat := 3
  /-- What the abstract handlers read. -/
  app         : Experiment.Config := {}

/-! ## The store -/

structure Store where
  docs : List (Ident × Promise × Version) := []

def send {σ : Type} (to : Addr) (m : CMsg) : H Config σ (Out CMsg) Unit := emit (.send to m)

def storeReceive (sender : Addr) (m : CMsg) : H Config Store (Out CMsg) Unit := do
  match m with
  | .get op key =>
    let doc := ((← get).docs.find? (·.1 == key)).map fun (_, p, v) => (p, v)
    send sender (.got op doc)
  | .put op key p ifMatch =>
    let cur := ((← get).docs.find? (·.1 == key)).map (·.2.2)
    let cfg ← read
    if cfg.conditional && ifMatch != cur then
      send sender (.conflict op)
    else
      -- 0: lands, and says so; 1: lands, and fails; 2: fails
      let fate ← if cfg.flaky then choose ⟨[0, 1, 2], by simp⟩ else pure 0
      if fate != 2 then
        modify fun s => { docs := (key, p, cur.getD 0 + 1) :: s.docs.filter (·.1 != key) }
      send sender (if fate == 0 then .written op else .failed op)
  | _ => pure ()

/-! ## A node -/

inductive Phase where
  | loading
  /-- Written, waiting for the store; then answer, and send what the step sent. -/
  | writing (res : Response) (outbox : List (Addr × Msg))

/-- A request in progress. -/
structure Flight where
  client  : Addr
  id      : CallId
  req     : Request
  attempt : Nat
  phase   : Phase

structure Node where
  nextOp  : OpId := 0
  flights : List (OpId × Flight) := []

abbrev NodeH := H Config Node (Out CMsg)

def fresh : NodeH OpId := do
  let n ← get
  set { n with nextOp := n.nextOp + 1 }
  return n.nextOp

/-- The flight waiting on `op`, if any, no longer waiting. -/
def takeFlight (op : OpId) : NodeH (Option Flight) := do
  let n ← get
  match n.flights.find? (·.1 == op) with
  | some (_, f) =>
    set { n with flights := n.flights.filter (·.1 != op) }
    return some f
  | none => return none

def await (f : Flight) (m : OpId → CMsg) : NodeH Unit := do
  let op ← fresh
  modify fun n => { n with flights := (op, f) :: n.flights }
  send (← read).store (m op)

def answer (f : Flight) (res : Response) : NodeH Unit := send f.client (.app (.res f.id res))

/-- The document is loaded: run the abstract handler on it. Nothing
    changed: answer now. Something did: write it, conditionally. -/
def decideStep (f : Flight) (doc : Option (Promise × Version)) (now : Time) : NodeH Unit := do
  let before : Experiment.State := { promises := doc.toList.map (·.1) }
  let (res, after, outs) := pick ((Experiment.request f.req now).run (← read).app before) 0
  for o in outs do
    match o with
    | .always n ok => emit (.always n ok)
    | .sometimes n hit => emit (.sometimes n hit)
    | .send _ _ => pure ()
  if after == before then
    answer f res
    for (a, m) in sends outs do send a (.app m)
  else
    match after.promises.find? (·.id == f.req.key) with
    | none => answer f { status := 503 }
    | some p =>
      await { f with phase := .writing res (sends outs) } fun op =>
        .put op f.req.key p (doc.map (·.2))

def nodeReceive (sender : Addr) (m : CMsg) (now : Time) : NodeH Unit := do
  match m with
  | .app (.req id r) =>
    await ⟨sender, id, r, 0, .loading⟩ fun op => .get op r.key
  | .got op doc =>
    match ← takeFlight op with
    | some f => decideStep f doc now
    | none => pure ()
  | .written op =>
    match ← takeFlight op with
    | some f =>
      match f.phase with
      | .writing res outbox =>
        answer f res
        for (a, m) in outbox do send a (.app m)
      | .loading => pure ()
    | none => pure ()
  | .conflict op =>
    match ← takeFlight op with
    | some f =>
      if f.attempt < (← read).retries then
        await { f with attempt := f.attempt + 1, phase := .loading } fun op => .get op f.req.key
      else
        answer f { status := 503 }
    | none => pure ()
  | .failed op =>
    match ← takeFlight op with
    | some f => answer f { status := 503 }
    | none => pure ()
  | _ => pure ()

/-! ## The system: every process runs this -/

inductive Local where
  | node (n : Node)
  | store (s : Store)

def receive (sender : Addr) (m : CMsg) (now : Time) : H Config Local (Out CMsg) Unit :=
  fun e s =>
    match s with
    | .node n => ((nodeReceive sender m now) e n).map fun (a, n', w) => (a, .node n', w)
    | .store st => ((storeReceive sender m) e st).map fun (a, st', w) => (a, .store st', w)

abbrev system : Service where
  Config  := Config
  State   := Local
  Msg     := CMsg
  receive := receive
  tick    := fun _ => pure ()

/-! ## Refinement, checked per run -/

/-- What the clients saw, as the abstract world's trace: every request
    sent and every message received, with its time. Nodes, the store, and
    which node a client asked are not in it. -/
def clientTrace (x : Network.Execution system) : List (Experiment.Label Msg) :=
  x.filterMap fun ((who, t, ev), _, _) =>
    match who, ev with
    | .client a, .request _ (.app m) => some (.client a, t, .request m)
    | .client a, .receive _ (.app m) => some (.client a, t, .receive .server m)
    | _, _ => none

/-- The clients saw a trace of the abstract service, which may fail any
    request (a node that loses too many races, or whose write fails, answers
    503). -/
def refines (cfg : Config) (x : Network.Execution system) : Bool :=
  Experiment.check Experiment.promises { cfg.app with unreliable := true } {} (clientTrace x)

end Experiment.Storage

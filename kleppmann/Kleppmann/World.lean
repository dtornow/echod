/-!
# A world to check traces in, in Kleppmann's shape

`Network.lean` is Kleppmann's model as he wrote it, for proving that every
execution has a property. This file is the same shape set up for the other
question: could this recorded trace have happened?

**Processes.** The `server`, whose step function is the model, and clients,
each at an address: a request typed in at a client is sent to the server,
and whatever the server sends a client is received there.

**Events.** Kleppmann's three, unchanged: a message is received, a user
types a request, a timeout fires. The environment chooses which process gets
which event next. A timeout is a tick: the process may do something, or
nothing.

**The rule.** His, with three changes, each marked where it is made:

1. **Time.** Every step happens at an instant `t`, never earlier than the
   step before. The model reads it as `now`.
2. **Outcomes.** A step has a list of possible results, not one: a model is
   a specification and may allow several behaviors.
3. **A received message is gone.** He never removes a message, so one may
   be received many times; here each is received at most once, so a
   request takes effect at most once.

**What a trace is.** Every step, with its time, except the server receiving
a request: no one outside sees when the server took it. That is the
linearization point, and the one thing a checker has to find. Timeouts are
in the trace: in a driven run (a test, a fuzzer, a server on debug time)
the ticks are what the driver did.
-/

namespace Kleppmann.World

abbrev Time := Nat
abbrev CallId := Nat
abbrev Client := String

/-- At least one. -/
abbrev Some (α : Type) := { xs : List α // xs ≠ [] }

def Some.one {α : Type} (x : α) : Some α := ⟨[x], by simp⟩

/-- What a request may do: the next state, the response, and what is sent
    to clients on the side. -/
structure ExternalOutcome (S R D : Type) where
  next : S
  resp : R
  send : List (Client × D) := []

/-- What a tick may do: the next state, and what is sent to clients. -/
structure TickOutcome (S D : Type) where
  next : S
  send : List (Client × D) := []

/-- The server. It reads the time and never moves it. -/
structure Model where
  State    : Type
  Request  : Type
  Response : Type
  Dispatch : Type
  /-- A request taking effect at `now`: every allowed outcome. -/
  external : Request → State → Time → Some (ExternalOutcome State Response Dispatch)
  /-- A tick at `now`: every allowed outcome. Doing nothing is one. -/
  tick     : State → Time → Some (TickOutcome State Dispatch)
  decRes   : DecidableEq Response := by infer_instance
  decDis   : DecidableEq Dispatch := by infer_instance

/-! ## The world -/

inductive Proc where
  | server
  | client (a : Client)
  deriving DecidableEq, Repr

variable {m : Model}

/-- What travels. -/
inductive Msg (m : Model) where
  /-- A client's request, under the client's id for it. -/
  | req (id : CallId) (r : m.Request)
  /-- The response to request `id`. -/
  | res (id : CallId) (r : m.Response)
  /-- Something the server sends a client on its own. -/
  | out (d : m.Dispatch)

/-- Kleppmann's events. -/
inductive Event (m : Model) where
  | receive (sender : Proc) (msg : Msg m)
  | request (id : CallId) (r : m.Request)
  | timeout

/-- Messages sent and not yet received, as (sender, recipient, message). -/
abbrev Net (m : Model) := List (Proc × Proc × Msg m)

structure Conf (m : Model) where
  net   : Net m
  state : m.State
  /-- The instant of the last step. -/
  now   : Time

/-- One possible result of a step: the server's next state, and what is sent. -/
structure Result (m : Model) where
  next : m.State
  sent : List (Proc × Msg m)

def outs (send : List (Client × m.Dispatch)) : List (Proc × Msg m) :=
  send.map fun (a, d) => (.client a, .out d)

/-- Each process's step function, at instant `t`. The server's is the
    model's; a client sends what is typed in, keeps what it receives, and
    ignores ticks. Anything else cannot happen. -/
def stepOf (s : m.State) (t : Time) : Proc → Event m → List (Result m)
  | .server, .receive (.client a) (.req id r) =>
      (m.external r s t).val.map fun o => ⟨o.next, (.client a, .res id o.resp) :: outs o.send⟩
  | .server, .timeout => (m.tick s t).val.map fun o => ⟨o.next, outs o.send⟩
  | .client _, .request id r => [⟨s, [(.server, .req id r)]⟩]
  | .client _, .receive .server _ => [⟨s, []⟩]
  | .client _, .timeout => [⟨s, []⟩]
  | _, _ => []

/-- Kleppmann's `valid_event`, with change 3: a received message was sent,
    to this process, and is taken off the network. -/
inductive Takes : Proc → Event m → Net m → Net m → Prop where
  | receive {p sender msg pre post} :
      Takes p (.receive sender msg) (pre ++ (sender, p, msg) :: post) (pre ++ post)
  | request {p id r net} : Takes p (.request id r) net net
  | timeout {p net} : Takes p .timeout net net

/-- **The rule.** -/
inductive Step (m : Model) : Conf m → Proc × Time × Event m → Conf m → Prop where
  | step {c p t ev net' res} :
      c.now ≤ t →                                              -- change 1
      Takes p ev c.net net' →
      res ∈ stepOf c.state t p ev →                            -- change 2
      Step m c (p, t, ev) ⟨net' ++ res.sent.map (fun (to, msg) => (p, to, msg)), res.next, t⟩

/-! ## Executions, and what a trace is -/

abbrev Execution (m : Model) := List ((Proc × Time × Event m) × Conf m)

def Legal (m : Model) : Conf m → Execution m → Prop
  | _, [] => True
  | c, (e, c') :: rest => Step m c e c' ∧ Legal m c' rest

/-- Whether a step is seen: all but the server receiving a request. -/
def Event.seenAt : Proc → Event m → Bool
  | .server, .receive _ _ => false
  | _, _ => true

/-- What an execution shows. -/
def observe : Execution m → List (Proc × Time × Event m)
  | [] => []
  | ((p, t, ev), _) :: rest => if Event.seenAt p ev then (p, t, ev) :: observe rest else observe rest

def initial (init : m.State) : Conf m := ⟨[], init, 0⟩

/-- The trace could have happened: some execution shows exactly it. -/
def Valid (m : Model) (init : m.State) (trace : List (Proc × Time × Event m)) : Prop :=
  ∃ x, Legal m (initial init) x ∧ observe x = trace

end Kleppmann.World

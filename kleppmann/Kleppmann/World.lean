/-!
# A world to check traces in, in Kleppmann's shape

`Network.lean` is Kleppmann's model as he wrote it: processes, events, one
network, one rule. It is for proving that every execution has a property.
This file is the same shape set up for the other question: could this
recorded trace have happened?

**The processes.** Three kinds:

* `sys`, the system, whose step function is the model (`external`, `tick`);
* `client a`, at address `a`: a request typed in is sent to `sys`, and
  anything `sys` sends is received;
* `clock`, whose only step moves the time forward.

**One rule.** A step is an event at a process. It takes the message it
receives off the network, runs the process's step function, and puts what
that sends on the network. Kleppmann's rule, with four changes, each
marked where it is made:

1. **Time.** The configuration has a clock; only the clock process moves
   it, forward. Every other step happens at the current instant.
2. **What is due goes first.** While the model says something is due
   (`due ≤ now`) and a tick can do something, the only step allowed is the
   system's tick.
3. **Outcomes.** A step has a list of possible results, not one: a model
   is a specification and may allow several behaviors.
4. **A received message is gone.** He never removes a message, so one may
   be received many times; here each is received at most once, so a
   request takes effect at most once.

**What a trace is.** The steps of the clients and the clock, in order:
everything except the system's. `Valid m init trace` says some execution
shows exactly those. The system's steps, when it received each request and
when it ticked, are what a checker has to find.
-/

namespace Kleppmann.World

abbrev Time := Nat
abbrev CallId := Nat
abbrev Client := String

/-- At least one: a request always has an outcome. -/
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

/-- The system. It reads the clock and never moves it. -/
structure Model where
  State    : Type
  Request  : Type
  Response : Type
  Dispatch : Type
  /-- A request taking effect, at `now`: every allowed outcome. -/
  external : Request → State → Time → Some (ExternalOutcome State Response Dispatch)
  /-- What the system may do on its own at `now`: one outcome per choice.
      Empty: nothing to do. -/
  tick     : State → Time → List (TickOutcome State Dispatch)
  /-- The earliest time something must have happened by, if any. While it
      has come and a tick can act, a tick goes first. -/
  due      : State → Option Time := fun _ => none
  decRes   : DecidableEq Response := by infer_instance
  decDis   : DecidableEq Dispatch := by infer_instance

/-! ## The world -/

inductive Proc where
  | sys
  | client (a : Client)
  | clock
  deriving DecidableEq, Repr

variable {m : Model}

/-- What travels. -/
inductive Msg (m : Model) where
  /-- A client's request, under the client's id for it. -/
  | req (id : CallId) (r : m.Request)
  /-- The response to request `id`. -/
  | res (id : CallId) (r : m.Response)
  /-- Something the system sends a client on its own. -/
  | out (d : m.Dispatch)

/-- What happens at a process in one step. -/
inductive Event (m : Model) where
  /-- Kleppmann's `Receive`. -/
  | receive (sender : Proc) (msg : Msg m)
  /-- Kleppmann's `Request`: user input at a client. -/
  | request (id : CallId) (r : m.Request)
  /-- Kleppmann's `Timeout`. -/
  | timeout
  /-- The clock moves to `t`. -/
  | time (t : Time)

/-- Messages sent and not yet received, as (sender, recipient, message). -/
abbrev Net (m : Model) := List (Proc × Proc × Msg m)

structure Conf (m : Model) where
  net   : Net m
  state : m.State
  now   : Time

/-- Something is due and a tick can act on it. -/
def Conf.Owed (c : Conf m) : Prop :=
  ∃ d, m.due c.state = some d ∧ d ≤ c.now ∧ m.tick c.state c.now ≠ []

/-- One possible result of a step: the system's next state, what is sent,
    and the instant after. -/
structure Result (m : Model) where
  next : m.State
  sent : List (Proc × Msg m)
  now  : Time

def outs (send : List (Client × m.Dispatch)) : List (Proc × Msg m) :=
  send.map fun (a, d) => (.client a, .out d)

/-- Each process's step function. The system's is the model's; a client
    sends what is typed in and keeps what it receives; the clock moves the
    time forward. Anything else cannot happen. -/
def stepOf (c : Conf m) : Proc → Event m → List (Result m)
  | .sys, .receive (.client a) (.req id r) =>
      (m.external r c.state c.now).val.map fun o =>
        ⟨o.next, (.client a, .res id o.resp) :: outs o.send, c.now⟩
  | .sys, .timeout =>
      (m.tick c.state c.now).map fun o => ⟨o.next, outs o.send, c.now⟩
  | .client _, .request id r => [⟨c.state, [(.sys, .req id r)], c.now⟩]
  | .client _, .receive .sys _ => [⟨c.state, [], c.now⟩]
  | .clock, .time t => if c.now ≤ t then [⟨c.state, [], t⟩] else []
  | _, _ => []

/-- Kleppmann's `valid_event`, with change 4: a received message was sent,
    to this process, and is taken off the network. -/
inductive Takes : Proc → Event m → Net m → Net m → Prop where
  | receive {p sender msg pre post} :
      Takes p (.receive sender msg) (pre ++ (sender, p, msg) :: post) (pre ++ post)
  | request {p id r net} : Takes p (.request id r) net net
  | timeout {p net} : Takes p .timeout net net
  | time {p t net} : Takes p (.time t) net net

/-- **The rule.** -/
inductive Step (m : Model) : Conf m → Proc × Event m → Conf m → Prop where
  | step {c p ev net' res} :
      Takes p ev c.net net' →
      (c.Owed → p = .sys ∧ ev = .timeout) →                    -- change 2
      res ∈ stepOf c p ev →                                    -- change 3
      Step m c (p, ev) ⟨net' ++ res.sent.map (fun (to, msg) => (p, to, msg)), res.next, res.now⟩

/-! ## Executions, and what a trace is -/

abbrev Execution (m : Model) := List ((Proc × Event m) × Conf m)

def Legal (m : Model) : Conf m → Execution m → Prop
  | _, [] => True
  | c, (e, c') :: rest => Step m c e c' ∧ Legal m c' rest

/-- What an execution shows: every step but the system's. -/
def observe : Execution m → List (Proc × Event m)
  | [] => []
  | ((p, ev), _) :: rest => if p = .sys then observe rest else (p, ev) :: observe rest

def initial (init : m.State) : Conf m := ⟨[], init, 0⟩

/-- The trace could have happened: some execution shows exactly it. -/
def Valid (m : Model) (init : m.State) (trace : List (Proc × Event m)) : Prop :=
  ∃ x, Legal m (initial init) x ∧ observe x = trace

end Kleppmann.World

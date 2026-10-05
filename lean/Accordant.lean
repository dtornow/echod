/-!
# What the accordant checker promises

In one sentence:

> If the checker accepts a trace, then some execution of the system,
> projected onto what clients observe, is exactly that trace.

In Lean, at the bottom of this file:

```
theorem soundness :
    check m init start trace = true → Valid m init start trace

def Valid m init start trace :=
  ∃ steps, Legal m (initial init start) steps ∧ project steps = trace
```

Everything above the theorem defines its words:

* `Event`: what a client observes.
* `Model`: the system.
* `Step`: how the system evolves; each step is observed or silent.
* `Legal`: a sequence of steps the system can actually take.
* `project`: what an execution shows a client.

`check` is the Rust checker with its default configuration:

```rust
Checker::new(m, init, Config { start, ..Config::default() }).check(trace).is_ok()
```

Lean can't see Rust code, so `check` is a name standing for that function and
the theorem is stated, not proved. `verus/accordant.rs` states the same theorem
on the Rust function itself.

Not covered: `assert_idle`, and request lifetimes (off by default). Known to
make the theorem false today: internal work spawned during a tick, with a
deadline before the tick's next stop, fires late (to be fixed in the checker).
-/

namespace Accordant

abbrev Time := Nat
abbrev CallId := Nat

/-! ## Observations: all a client ever sees -/

inductive Event (X R D : Type) where
  /-- The client sent a request. -/
  | invoke (time : Time) (call : CallId) (req : X)
  /-- The client got the response to that call. -/
  | ret (time : Time) (call : CallId) (res : R)
  /-- The client got a dispatch the server sent on its own. -/
  | receive (time : Time) (msg : D)

/-! ## The system -/

/-- Internal work to start, and when it runs. -/
inductive Sched (I : Type) where
  | later (req : I)                  -- from now on; must happen eventually
  | timer (at_ : Time) (req : I)     -- exactly at the given time
  | after (at_ : Time) (req : I)     -- not before the given time; must happen eventually
  | within (d : Time) (req : I)      -- from now on; within the given duration
  | maybe (req : I)                  -- from now on, or never

/-- One possible effect of a request. -/
structure ExternalOutcome (S R I D : Type) where
  next  : S
  res   : R
  spawn : List (Sched I)
  send  : List D

/-- One possible effect of internal work. -/
structure InternalOutcome (S I D : Type) where
  next  : S
  spawn : List (Sched I)
  send  : List D

/-- The system: requests from clients, work it does on its own. -/
structure Model where
  State    : Type
  External : Type
  Response : Type
  Internal : Type
  Dispatch : Type
  /-- A request takes effect: every allowed outcome. -/
  external : External → State → Time → List (ExternalOutcome State Response Internal Dispatch)
  /-- Internal work runs: every possible outcome. Empty: it can't run now. -/
  internal : Internal → State → Time → List (InternalOutcome State Internal Dispatch)
  /-- Whether a client seeing `observed` matches the `expected` response. -/
  admits   : Response → Response → Bool

abbrev Model.Ev (m : Model) := Event m.External m.Response m.Dispatch

/-! ## Configurations: everything about the system at one point, seen or not -/

/-- A call the client has sent and not yet seen answered. -/
inductive Call (X R : Type) where
  | inFlight (req : X)   -- not yet taken effect
  | done (res : R)       -- taken effect; the client will see this response

/-- Internal work started and not yet run. -/
structure Work (I : Type) where
  req   : I
  after : Time          -- can't run before this
  due   : Option Time   -- must have run by this time, if it can run then
  must  : Bool          -- must run at some point (false: `maybe`)

structure Config (m : Model) where
  state : m.State
  now   : Time
  calls : CallId → Option (Call m.External m.Response)
  work  : List (Work m.Internal)
  sent  : List m.Dispatch   -- dispatches sent, not yet received

def schedule {I : Type} (now : Time) : Sched I → Work I
  | .later r    => ⟨r, now, none, true⟩
  | .timer t r  => ⟨r, max t now, some (max t now), true⟩
  | .after t r  => ⟨r, max t now, none, true⟩
  | .within d r => ⟨r, now, some (now + d), true⟩
  | .maybe r    => ⟨r, now, none, false⟩

def update {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

variable {m : Model}

/-- Work whose deadline has come and that can run: it runs before anything else. -/
def Config.overdue (c : Config m) : Prop :=
  ∃ w ∈ c.work, w.must = true ∧ w.after ≤ c.now ∧
    (∃ d, w.due = some d ∧ d ≤ c.now) ∧ m.internal w.req c.state c.now ≠ []

/-- Time may move to `t` only if it doesn't skip a deadline. Work whose deadline
    has come and that can't run then owes nothing. -/
def Config.mayAdvance (c : Config m) (t : Time) : Prop :=
  c.now < t ∧ ∀ w ∈ c.work, w.must = true → ∀ d, w.due = some d →
    t ≤ d ∨ (d ≤ c.now ∧ m.internal w.req c.state c.now = [])

/-! ## Steps: how the system evolves, and what each step shows a client -/

/-- A step either shows a client an event, or nothing. -/
inductive Label (m : Model) where
  | obs (e : m.Ev)
  | silent

inductive Step (m : Model) : Config m → Label m → Config m → Prop where
  /-- A client sends a request. Observed. -/
  | invoke {c : Config m} {call req} :
      c.calls call = none → ¬ c.overdue →
      Step m c (.obs (.invoke c.now call req))
        { c with calls := update c.calls call (some (.inFlight req)) }
  /-- A client receives the response its call took effect with. Observed. -/
  | ret {c : Config m} {call expected res} :
      c.calls call = some (.done expected) → m.admits expected res = true → ¬ c.overdue →
      Step m c (.obs (.ret c.now call res)) { c with calls := update c.calls call none }
  /-- A client receives a dispatch that was sent and not yet received. Observed. -/
  | receive {c : Config m} {pre post msg} :
      c.sent = pre ++ msg :: post → ¬ c.overdue →
      Step m c (.obs (.receive c.now msg)) { c with sent := pre ++ post }
  /-- A call in flight takes effect with one of its allowed outcomes. Silent. -/
  | effect {c : Config m} {call req o} :
      c.calls call = some (.inFlight req) → o ∈ m.external req c.state c.now → ¬ c.overdue →
      Step m c .silent
        { c with state := o.next
                 calls := update c.calls call (some (.done o.res))
                 work  := c.work ++ o.spawn.map (schedule c.now)
                 sent  := c.sent ++ o.send }
  /-- Pending internal work runs with one of its outcomes; while some work is
      overdue, only overdue work runs. Silent. -/
  | run {c : Config m} {pre post w o} :
      c.work = pre ++ w :: post → w.after ≤ c.now → o ∈ m.internal w.req c.state c.now →
      (c.overdue → w.must = true ∧ ∃ d, w.due = some d ∧ d ≤ c.now) →
      Step m c .silent
        { c with state := o.next
                 work  := pre ++ post ++ o.spawn.map (schedule c.now)
                 sent  := c.sent ++ o.send }
  /-- Time passes. Silent. -/
  | advance {c : Config m} {t} :
      c.mayAdvance t → Step m c .silent { c with now := t }

/-! ## Executions, and what they show a client -/

/-- An execution: the steps taken from a starting configuration, each with the
    configuration it leads to. -/
abbrev Execution (m : Model) := List (Label m × Config m)

/-- The system can take these steps, one after the other, starting from `c`. -/
def Legal (m : Model) : Config m → Execution m → Prop
  | _, [] => True
  | c, (l, c') :: rest => Step m c l c' ∧ Legal m c' rest

/-- What an execution shows a client: its observed events, in order. Silent
    steps show nothing. -/
def project : Execution m → List m.Ev
  | [] => []
  | (.obs e, _) :: rest => e :: project rest
  | (.silent, _) :: rest => project rest

def initial (init : m.State) (start : Time) : Config m :=
  ⟨init, start, fun _ => none, [], []⟩

/-- The trace is valid: some execution of the system, from `init` at `start`,
    projected onto what clients observe, is exactly the trace. -/
def Valid (m : Model) (init : m.State) (start : Time) (trace : List m.Ev) : Prop :=
  ∃ steps, Legal m (initial init start) steps ∧ project steps = trace

/-! ## The theorem -/

/-- The Rust checker:
    `Checker::new(m, init, Config { start, ..Config::default() }).check(trace).is_ok()`. -/
opaque check (m : Model) (init : m.State) (start : Time) (trace : List m.Ev) : Bool

/-- Soundness: if the checker accepts a trace, the trace is valid. Stated, not proved. -/
theorem soundness (m : Model) (init : m.State) (start : Time) (trace : List m.Ev) :
    check m init start trace = true → Valid m init start trace := by
  sorry

/-! ## Examples, proved -/

/-- For every model, the empty trace is valid: the execution with no steps. -/
theorem empty_trace_valid (m : Model) (init : m.State) (start : Time) :
    Valid m init start [] :=
  ⟨[], trivial, rfl⟩

/-- A counter: `incr` takes effect and answers the new value. -/
abbrev counter : Model where
  State    := Nat
  External := Unit
  Response := Nat
  Internal := Empty
  Dispatch := Empty
  external := fun _ n _ => [⟨n + 1, n + 1, [], []⟩]
  internal := fun e _ _ => nomatch e
  admits   := fun expected observed => expected == observed

abbrev incr : ExternalOutcome Nat Nat Empty Empty := ⟨1, 1, [], []⟩

/-- Sent at 0, answered 1 at 0: valid. The execution is invoke (observed),
    effect (silent), return (observed). -/
example : Valid counter (0 : Nat) 0 [.invoke 0 7 (), .ret 0 7 1] := by
  refine ⟨[(.obs (.invoke 0 7 ()), _), (.silent, _), (.obs (.ret 0 7 1), _)],
    ⟨.invoke ?_ ?_, .effect (call := 7) (req := ()) (o := incr) ?_ ?_ ?_,
     .ret (expected := (1 : Nat)) ?_ ?_ ?_, trivial⟩, rfl⟩
  all_goals simp [initial, update, Config.overdue, counter]

end Accordant

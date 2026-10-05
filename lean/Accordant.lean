/-!
# What the accordant checker promises

In one sentence:

> If the checker accepts a trace, then some execution of the system,
> projected onto what clients observe, is exactly that trace.

In Lean, at the bottom of this file:

```
theorem soundness :
    check m init trace = true → Valid m init trace

def Valid m init trace :=
  ∃ steps, Legal m (initial init) steps ∧ project steps = trace
```

The first part of the file defines the words:

* `Event`: what a client observes.
* `Model`: the system.
* `Step`: how the system evolves; each step is observed or silent.
* `Legal`: a sequence of steps the system can actually take.
* `project`: what an execution shows a client.

`check` is the Rust checker with certificates:

```rust
Checker::new(m, init, Config::default()).check_certified(trace).is_ok()
```

The checker searches for an execution and reports it as a list of moves, a
certificate. Before accepting, it replays the moves with `certify`, which must
show exactly the trace. The second part of the file defines `certify` and proves
`accepted_valid`: whatever `certify` accepts is valid. `soundness` follows from
one assumption, that the Rust `certify` (`src/certificate.rs`) computes what the
Lean one does. Lean can't see Rust code, so that one assumption stays. The
search itself needs no proof.

Not covered: `assert_idle`, and request lifetimes (off by default).
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

/-- The system starts in `init` at time 0, with nothing in flight. Starting at 0
    loses nothing: time passing is a silent step, so an execution moves the
    clock to the first event's time on its own. -/
def initial (init : m.State) : Config m :=
  ⟨init, 0, fun _ => none, [], []⟩

/-- The trace is valid: some execution of the system, from `initial init`,
    projected onto what clients observe, is exactly the trace. -/
def Valid (m : Model) (init : m.State) (trace : List m.Ev) : Prop :=
  ∃ steps, Legal m (initial init) steps ∧ project steps = trace

/-! ## Certificates: checking an execution someone found

Finding an execution is hard: the checker searches. Checking one is easy: walk
it, one step at a time. A certificate is the list of moves the checker found,
each naming which call, work, dispatch or outcome it takes; `replay` rebuilds
the configurations and fails on the first move the system can't make. -/

/-- One move of an execution, as the checker reports it. -/
inductive Move (m : Model) where
  | invoke (call : CallId) (req : m.External)
  | ret (call : CallId) (res : m.Response)
  /-- Receive the `i`-th dispatch sent and not yet received. -/
  | receive (i : Nat)
  /-- The call takes effect with the `j`-th of its outcomes. -/
  | effect (call : CallId) (j : Nat)
  /-- The `i`-th pending work runs with the `j`-th of its outcomes. -/
  | run (i j : Nat)
  | advance (t : Time)

/-- `overdue` and `mayAdvance`, computed. -/
def Work.isOverdue (c : Config m) (w : Work m.Internal) : Bool :=
  w.must && decide (w.after ≤ c.now) &&
    (match w.due with | some d => decide (d ≤ c.now) | none => false) &&
    !(m.internal w.req c.state c.now).isEmpty

def Config.isOverdue (c : Config m) : Bool := c.work.any (Work.isOverdue c)

def Config.canAdvance (c : Config m) (t : Time) : Bool :=
  decide (c.now < t) && c.work.all fun w =>
    !w.must || match w.due with
      | none => true
      | some d => decide (t ≤ d) || (decide (d ≤ c.now) && (m.internal w.req c.state c.now).isEmpty)

/-- One move from `c`: the step's label and where it leads, if the system can make it. -/
def Config.move (c : Config m) : Move m → Option (Label m × Config m)
  | .invoke call req =>
      if (c.calls call).isNone && !c.isOverdue then
        some (.obs (.invoke c.now call req), { c with calls := update c.calls call (some (.inFlight req)) })
      else none
  | .ret call res =>
      match c.calls call with
      | some (.done expected) =>
          if m.admits expected res && !c.isOverdue then
            some (.obs (.ret c.now call res), { c with calls := update c.calls call none })
          else none
      | _ => none
  | .receive i =>
      match c.sent[i]? with
      | some msg =>
          if !c.isOverdue then
            some (.obs (.receive c.now msg), { c with sent := c.sent.take i ++ c.sent.drop (i + 1) })
          else none
      | none => none
  | .effect call j =>
      match c.calls call with
      | some (.inFlight req) =>
          match (m.external req c.state c.now)[j]? with
          | some o =>
              if !c.isOverdue then
                some (.silent, { c with state := o.next
                                        calls := update c.calls call (some (.done o.res))
                                        work  := c.work ++ o.spawn.map (schedule c.now)
                                        sent  := c.sent ++ o.send })
              else none
          | none => none
      | _ => none
  | .run i j =>
      match c.work[i]? with
      | some w =>
          match (m.internal w.req c.state c.now)[j]? with
          | some o =>
              if decide (w.after ≤ c.now) && (!c.isOverdue || w.isOverdue c) then
                some (.silent, { c with state := o.next
                                        work  := c.work.take i ++ c.work.drop (i + 1) ++ o.spawn.map (schedule c.now)
                                        sent  := c.sent ++ o.send })
              else none
          | none => none
      | none => none
  | .advance t => if c.canAdvance t then some (.silent, { c with now := t }) else none

/-- Replays moves from `c`: the execution they make, if every move is legal. -/
def replay (c : Config m) : List (Move m) → Option (Execution m)
  | [] => some []
  | mv :: rest =>
      match c.move mv with
      | none => none
      | some (l, c') => (replay c' rest).map ((l, c') :: ·)

/-- What a certificate shows a client, if every move in it is legal. -/
def certify (m : Model) (init : m.State) (moves : List (Move m)) : Option (List m.Ev) :=
  (replay (initial init) moves).map project

/-- A trace is accepted when some certificate shows exactly it. -/
def Accepted (m : Model) (init : m.State) (trace : List m.Ev) : Prop :=
  ∃ moves, certify m init moves = some trace

theorem not_overdue {c : Config m} (h : c.isOverdue = false) : ¬ c.overdue := by
  rintro ⟨w, hw, hm, ha, ⟨d, hd, hdn⟩, hi⟩
  have : c.isOverdue = true := List.any_eq_true.mpr ⟨w, hw, by
    simp [Work.isOverdue, hm, ha, hd, hdn, hi]⟩
  simp_all

theorem overdue_work {c : Config m} {w : Work m.Internal} (h : w.isOverdue c = true) :
    w.must = true ∧ ∃ d, w.due = some d ∧ d ≤ c.now := by
  simp only [Work.isOverdue, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hm, _⟩, hd⟩, _⟩ := h
  refine ⟨hm, ?_⟩
  cases hdue : w.due with
  | none => simp [hdue] at hd
  | some d => exact ⟨d, rfl, by simpa [hdue] using hd⟩

theorem may_advance {c : Config m} {t : Time} (h : c.canAdvance t = true) : c.mayAdvance t := by
  simp only [Config.canAdvance, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  refine ⟨h.1, fun w hw hm d hd => ?_⟩
  have := h.2 w hw
  simp [hm, hd, List.isEmpty_iff] at this
  omega

theorem split_at {α : Type} {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) :
    l = l.take i ++ a :: l.drop (i + 1) := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp h
  rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]

theorem move_step {c c' : Config m} {mv : Move m} {l : Label m}
    (h : c.move mv = some (l, c')) : Step m c l c' := by
  cases mv with
  | invoke call req =>
    simp only [Config.move] at h
    split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rename_i hc
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.not_eq_true'] at hc
    exact .invoke hc.1 (not_overdue hc.2)
  | ret call res =>
    simp only [Config.move] at h
    split at h <;> try simp at h
    rename_i expected hcall
    obtain ⟨⟨ha, ho⟩, rfl, rfl⟩ := h
    exact .ret hcall ha (not_overdue ho)
  | receive i =>
    simp only [Config.move] at h
    split at h <;> try simp at h
    rename_i msg hmsg
    obtain ⟨ho, rfl, rfl⟩ := h
    exact .receive (split_at hmsg) (not_overdue ho)
  | effect call j =>
    simp only [Config.move] at h
    split at h <;> try simp at h
    rename_i req hcall
    split at h <;> try simp at h
    rename_i o hout
    obtain ⟨ho, rfl, rfl⟩ := h
    exact .effect hcall (List.mem_of_getElem? hout) (not_overdue ho)
  | run i j =>
    simp only [Config.move] at h
    split at h <;> try simp at h
    rename_i w hw
    split at h <;> try simp at h
    rename_i o hout
    obtain ⟨⟨ha, hc⟩, rfl, rfl⟩ := h
    rw [← List.append_assoc]
    refine .run (split_at hw) ha (List.mem_of_getElem? hout) fun hov => ?_
    rcases hc with hno | hyes
    · exact absurd hov (not_overdue hno)
    · exact overdue_work hyes
  | advance t =>
    simp only [Config.move] at h
    split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rename_i hc
    exact .advance (may_advance hc)

theorem replay_legal {c : Config m} {moves : List (Move m)} {x : Execution m}
    (h : replay c moves = some x) : Legal m c x := by
  induction moves generalizing c x with
  | nil => simp [replay] at h; subst h; trivial
  | cons mv rest ih =>
    simp only [replay] at h
    split at h
    · simp at h
    · rename_i l c' hmv
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp h
      exact ⟨move_step hmv, ih hy⟩

/-- Checking a certificate is enough: whatever it shows is valid. Proved. -/
theorem accepted_valid {m : Model} {init : m.State} {trace : List m.Ev}
    (h : Accepted m init trace) : Valid m init trace := by
  obtain ⟨moves, hm⟩ := h
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hm
  exact ⟨x, replay_legal hx, rfl⟩

/-! ## The theorem -/

/-- The Rust checker, with certificates:
    `Checker::new(m, init, Config::default()).check_certified(trace).is_ok()`.
    It searches for an execution, then runs its own `certify` on the moves it
    found and compares what they show with the trace. -/
opaque check (m : Model) (init : m.State) (trace : List m.Ev) : Bool

/-- Soundness: if the checker accepts a trace, the trace is valid. Proved, from
    one assumption about the Rust code: its `certify` computes what Lean's does,
    so whatever it accepts has a certificate. The search needs no proof at all. -/
theorem soundness (m : Model) (init : m.State) (trace : List m.Ev)
    (rust_certify : check m init trace = true → Accepted m init trace) :
    check m init trace = true → Valid m init trace :=
  fun h => accepted_valid (rust_certify h)

/-! ## Examples, proved -/

/-- For every model, the empty trace is valid: the execution with no steps. -/
theorem empty_trace_valid (m : Model) (init : m.State) :
    Valid m init [] :=
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
example : Valid counter (0 : Nat) [.invoke 0 7 (), .ret 0 7 1] := by
  refine ⟨[(.obs (.invoke 0 7 ()), _), (.silent, _), (.obs (.ret 0 7 1), _)],
    ⟨.invoke ?_ ?_, .effect (call := 7) (req := ()) (o := incr) ?_ ?_ ?_,
     .ret (expected := (1 : Nat)) ?_ ?_ ?_, trivial⟩, rfl⟩
  all_goals simp [initial, update, Config.overdue, counter]

end Accordant

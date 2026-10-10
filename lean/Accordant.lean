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

* `Event`: what a client observes. No time: a trace's order is the order one
  observer saw.
* `Model`: the system. Time is the model's own: its state has a clock (`now`),
  moved by its own steps (a request like `AdvanceClock`), and deadlines are on
  that clock.
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
-/

namespace Accordant

abbrev Time := Nat
abbrev CallId := Nat

/-! ## Observations: all a client ever sees -/

inductive Event (X R D : Type) where
  /-- The client sent a request. -/
  | invoke (call : CallId) (req : X)
  /-- The client got the response to that call. -/
  | ret (call : CallId) (res : R)
  /-- The client got a dispatch the server sent on its own. -/
  | receive (msg : D)

/-! ## The system -/

/-- Internal work to start, and when it runs, on the model's clock. -/
inductive Sched (I : Type) where
  | later (req : I)                  -- from now on, or never
  | timer (at_ : Time) (req : I)     -- at the given time

/-- One possible effect of a request. -/
structure ExternalOutcome (S R I D : Type) where
  next : S
  resp : R
  work : List (Sched I)
  send : List D

/-- One possible effect of internal work. -/
structure InternalOutcome (S I D : Type) where
  next : S
  work : List (Sched I)
  send : List D

/-- At least one. Nondeterminism is a list of alternatives; this is a list
    that can't be empty, so a request can't be refused. -/
abbrev Some (α : Type) := { xs : List α // xs ≠ [] }

/-- Exactly one. -/
def Some.one {α : Type} (x : α) : Some α := ⟨[x], by simp⟩

/-- The system: requests from clients, work it does on its own, and its clock. -/
structure Model where
  State    : Type
  External : Type
  Response : Type
  Internal : Type
  Dispatch : Type
  /-- A request takes effect: every allowed outcome. At least one: every
      request is accepted in every state (input-enabled). -/
  external : External → State → Some (ExternalOutcome State Response Internal Dispatch)
  /-- Internal work runs: every possible outcome. Empty: it can't run now. -/
  internal : Internal → State → List (InternalOutcome State Internal Dispatch)
  /-- The model's clock in a state. -/
  now      : State → Time
  /-- Responses can be compared: a client sees exactly the predicted one. -/
  decEq    : DecidableEq Response := by infer_instance
  /-- Dispatches can be compared: a client receives one by its value. -/
  decEqDispatch : DecidableEq Dispatch := by infer_instance

abbrev Model.Ev (m : Model) := Event m.External m.Response m.Dispatch

/-! ## Configurations: everything about the system at one point, seen or not -/

/-- A call the client has sent and not yet seen answered. -/
inductive Call (X R : Type) where
  | inFlight (req : X)   -- not yet taken effect
  | done (res : R)       -- taken effect; the client will see this response

/-- Internal work started and not yet run. Times are on the model's clock. -/
structure Work (I : Type) where
  req   : I
  after : Time          -- can't run before this
  due   : Option Time   -- must have run by this time, if it can run then
  must  : Bool          -- must run at some point (false: `maybe`)

structure Config (m : Model) where
  state : m.State
  calls : CallId → Option (Call m.External m.Response)
  work  : List (Work m.Internal)
  sent  : List m.Dispatch   -- dispatches sent, not yet received

/-- Work started at time `now`. -/
def schedule {I : Type} (now : Time) : Sched I → Work I
  | .later r    => ⟨r, now, none, true⟩
  | .timer t r  => ⟨r, max t now, some (max t now), true⟩

def update {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

variable {m : Model}

/-- Work whose deadline has come on the model's clock, and that can run. -/
def Config.Overdue (c : Config m) (w : Work m.Internal) : Prop :=
  w.must = true ∧ w.after ≤ m.now c.state ∧
    (∃ d, w.due = some d ∧ d ≤ m.now c.state) ∧ m.internal w.req c.state ≠ []

/-- Some work is overdue: it runs before anything else happens. -/
def Config.overdue (c : Config m) : Prop := ∃ w ∈ c.work, c.Overdue w

/-- `w` is overdue with the earliest deadline: when the clock jumped past
    several deadlines, their work runs in deadline order. -/
def Config.First (c : Config m) (w : Work m.Internal) : Prop :=
  c.Overdue w ∧ ∀ v ∈ c.work, c.Overdue v → ∃ d e, w.due = some d ∧ v.due = some e ∧ d ≤ e

/-! ## Steps: how the system evolves, and what each step shows a client -/

/-- A step either shows a client an event, or nothing. -/
inductive Label (m : Model) where
  | obs (e : m.Ev)
  | silent

inductive Step (m : Model) : Config m → Label m → Config m → Prop where
  /-- A client sends a request. Observed. -/
  | invoke {c : Config m} {call req} :
      c.calls call = none → ¬ c.overdue →
      Step m c (.obs (.invoke call req))
        { c with calls := update c.calls call (some (.inFlight req)) }
  /-- A client receives the response its call took effect with. Observed. -/
  | ret {c : Config m} {call res} :
      c.calls call = some (.done res) → ¬ c.overdue →
      Step m c (.obs (.ret call res)) { c with calls := update c.calls call none }
  /-- A client receives a dispatch that was sent and not yet received. Observed. -/
  | receive {c : Config m} {pre post msg} :
      c.sent = pre ++ msg :: post → ¬ c.overdue →
      Step m c (.obs (.receive msg)) { c with sent := pre ++ post }
  /-- A call in flight takes effect with one of its allowed outcomes. The work
      it starts is on the clock of the state it leads to. Silent. -/
  | effect {c : Config m} {call req o} :
      c.calls call = some (.inFlight req) → o ∈ (m.external req c.state).val → ¬ c.overdue →
      Step m c .silent
        { c with state := o.next
                 calls := update c.calls call (some (.done o.resp))
                 work  := c.work ++ o.work.map (schedule (m.now o.next))
                 sent  := c.sent ++ o.send }
  /-- Pending internal work runs with one of its outcomes; while some work is
      overdue, only overdue work with the earliest deadline runs. Silent. -/
  | run {c : Config m} {pre post w o} :
      c.work = pre ++ w :: post → w.after ≤ m.now c.state → o ∈ m.internal w.req c.state →
      (c.overdue → c.First w) →
      Step m c .silent
        { c with state := o.next
                 work  := pre ++ post ++ o.work.map (schedule (m.now o.next))
                 sent  := c.sent ++ o.send }

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

/-- The system starts in `init`, with nothing in flight. -/
def initial (init : m.State) : Config m :=
  ⟨init, fun _ => none, [], []⟩

/-- The trace is valid: some execution of the system, from `initial init`,
    projected onto what clients observe, is exactly the trace. -/
def Valid (m : Model) (init : m.State) (trace : List m.Ev) : Prop :=
  ∃ steps, Legal m (initial init) steps ∧ project steps = trace

/-! ## Certificates: checking an execution someone found

Finding an execution is hard: the checker searches. Checking one is easy: walk
it, one step at a time. The trace already has the observed steps; a
certificate adds the silent ones the checker found, each naming which call or
work and which outcome. `replay` rebuilds the configurations and fails on the
first step the system can't make. -/

/-- A silent step, as a certificate names it. -/
inductive Silent where
  /-- The call takes effect with the `j`-th of its outcomes. -/
  | effect (call : CallId) (j : Nat)
  /-- The `i`-th pending work runs with the `j`-th of its outcomes. -/
  | run (i j : Nat)

/-- A certificate: for each event of the trace, the silent steps just before it. -/
abbrev Certificate := List (List Silent)

/-- One step of the replay: an event of the trace, or a silent step. -/
inductive Move (m : Model) where
  | obs (e : m.Ev)
  | silent (s : Silent)

/-- `l` without the first `x` in it, if there is one. -/
def removeFirst {D : Type} [DecidableEq D] (x : D) : List D → Option (List D)
  | [] => none
  | y :: ys => if x = y then some ys else (removeFirst x ys).map (y :: ·)

/-- `Overdue`, `overdue` and `First`, computed. -/
def Work.isOverdue (c : Config m) (w : Work m.Internal) : Bool :=
  w.must && decide (w.after ≤ m.now c.state) &&
    (match w.due with | some d => decide (d ≤ m.now c.state) | none => false) &&
    !(m.internal w.req c.state).isEmpty

def Config.isOverdue (c : Config m) : Bool := c.work.any (Work.isOverdue c)

def dueLe {I : Type} (w v : Work I) : Bool :=
  match w.due, v.due with
  | some d, some e => decide (d ≤ e)
  | _, _ => false

/-- Whether `w` may run: nothing is overdue, or `w` is overdue with the
    earliest deadline. -/
def Config.mayRun (c : Config m) (w : Work m.Internal) : Bool :=
  !c.isOverdue || (w.isOverdue c && c.work.all fun v => !v.isOverdue c || dueLe w v)

/-- One move from `c`: the step's label and where it leads, if the system can make it. -/
def Config.move (c : Config m) : Move m → Option (Label m × Config m)
  | .obs (.invoke call req) =>
      if (c.calls call).isNone && !c.isOverdue then
        some (.obs (.invoke call req), { c with calls := update c.calls call (some (.inFlight req)) })
      else none
  | .obs (.ret call res) =>
      match c.calls call with
      | some (.done expected) =>
          if @decide (expected = res) (m.decEq expected res) && !c.isOverdue then
            some (.obs (.ret call res), { c with calls := update c.calls call none })
          else none
      | _ => none
  | .obs (.receive msg) =>
      match @removeFirst _ m.decEqDispatch msg c.sent with
      | some rest =>
          if !c.isOverdue then
            some (.obs (.receive msg), { c with sent := rest })
          else none
      | none => none
  | .silent (.effect call j) =>
      match c.calls call with
      | some (.inFlight req) =>
          match (m.external req c.state).val[j]? with
          | some o =>
              if !c.isOverdue then
                some (.silent, { c with state := o.next
                                        calls := update c.calls call (some (.done o.resp))
                                        work  := c.work ++ o.work.map (schedule (m.now o.next))
                                        sent  := c.sent ++ o.send })
              else none
          | none => none
      | _ => none
  | .silent (.run i j) =>
      match c.work[i]? with
      | some w =>
          match (m.internal w.req c.state)[j]? with
          | some o =>
              if decide (w.after ≤ m.now c.state) && c.mayRun w then
                some (.silent, { c with state := o.next
                                        work  := c.work.take i ++ c.work.drop (i + 1) ++
                                                   o.work.map (schedule (m.now o.next))
                                        sent  := c.sent ++ o.send })
              else none
          | none => none
      | none => none

/-- Replays moves from `c`: the execution they make, if every move is legal. -/
def replay (c : Config m) : List (Move m) → Option (Execution m)
  | [] => some []
  | mv :: rest =>
      match c.move mv with
      | none => none
      | some (l, c') => (replay c' rest).map ((l, c') :: ·)

/-- The trace and a certificate as one list of steps: each event after the
    silent steps the certificate puts before it. -/
def moves : List m.Ev → Certificate → List (Move m)
  | e :: es, ss :: rest => ss.map .silent ++ .obs e :: moves es rest
  | _, _ => []

/-- What a trace with a certificate shows a client, if every step is legal. -/
def certify (m : Model) (init : m.State) (trace : List m.Ev) (cert : Certificate) : Option (List m.Ev) :=
  (replay (initial init) (moves trace cert)).map project

/-- A trace is accepted when it has a certificate that shows exactly it. -/
def Accepted (m : Model) (init : m.State) (trace : List m.Ev) : Prop :=
  ∃ cert, certify m init trace cert = some trace

theorem isOverdue_iff {c : Config m} {w : Work m.Internal} :
    w.isOverdue c = true ↔ c.Overdue w := by
  unfold Work.isOverdue Config.Overdue
  cases w.due <;> simp [and_assoc]

theorem not_overdue {c : Config m} (h : c.isOverdue = false) : ¬ c.overdue := by
  rintro ⟨w, hw, hov⟩
  have : c.isOverdue = true := List.any_eq_true.mpr ⟨w, hw, isOverdue_iff.mpr hov⟩
  simp_all

theorem may_run {c : Config m} {w : Work m.Internal} (h : c.mayRun w = true) :
    c.overdue → c.First w := by
  intro hov
  simp only [Config.mayRun, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true,
    List.all_eq_true] at h
  rcases h with hno | ⟨hw, hall⟩
  · exact absurd hov (not_overdue hno)
  · refine ⟨isOverdue_iff.mp hw, fun v hv hvo => ?_⟩
    have hle := hall v hv
    try simp only [Bool.or_eq_true, Bool.not_eq_true'] at hle
    rcases hle with hf | hle
    · rw [isOverdue_iff.mpr hvo] at hf; contradiction
    · unfold dueLe at hle
      split at hle
      · rename_i d e hd he
        exact ⟨d, e, hd, he, by simpa using hle⟩
      · contradiction

theorem split_at {α : Type} {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) :
    l = l.take i ++ a :: l.drop (i + 1) := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp h
  rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]

theorem removeFirst_split {D : Type} [DecidableEq D] {x : D} {l l' : List D}
    (h : removeFirst x l = some l') : ∃ pre post, l = pre ++ x :: post ∧ l' = pre ++ post := by
  induction l generalizing l' with
  | nil => simp [removeFirst] at h
  | cons y ys ih =>
    simp only [removeFirst] at h
    split at h
    · rename_i hxy
      subst hxy
      exact ⟨[], ys, rfl, by simpa using h.symm⟩
    · obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨pre, post, h1, h2⟩ := ih hz
      exact ⟨y :: pre, post, by simp [h1], by simp [h2]⟩

theorem move_step {c c' : Config m} {mv : Move m} {l : Label m}
    (h : c.move mv = some (l, c')) : Step m c l c' := by
  cases mv with
  | obs e =>
    cases e with
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
        subst ha
        exact .ret hcall (not_overdue ho)
      | receive msg =>
        simp only [Config.move] at h
        split at h <;> try simp at h
        rename_i rest hrest
        obtain ⟨ho, rfl, rfl⟩ := h
        obtain ⟨pre, post, h1, h2⟩ := @removeFirst_split _ m.decEqDispatch _ _ _ hrest
        rw [h2]
        exact .receive h1 (not_overdue ho)
  | silent s =>
    cases s with
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
        exact .run (split_at hw) ha (List.mem_of_getElem? hout) (may_run hc)

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
  obtain ⟨cert, hm⟩ := h
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

/-- A counter: `incr` takes effect and answers the new value. No clock. -/
abbrev counter : Model where
  State    := Nat
  External := Unit
  Response := Nat
  Internal := Empty
  Dispatch := Empty
  external := fun _ n => .one ⟨n + 1, n + 1, [], []⟩
  internal := fun e _ => nomatch e
  now      := fun _ => 0

abbrev incr : ExternalOutcome Nat Nat Empty Empty := ⟨1, 1, [], []⟩

/-- Sent, then answered 1: valid. The execution is invoke (observed), effect
    (silent), return (observed). -/
example : Valid counter (0 : Nat) [.invoke 7 (), .ret 7 1] := by
  refine ⟨[(.obs (.invoke 7 ()), _), (.silent, _), (.obs (.ret 7 1), _)],
    ⟨.invoke ?_ ?_, .effect (call := 7) (req := ()) (o := incr) ?_ ?_ ?_,
     .ret ?_ ?_, trivial⟩, rfl⟩
  all_goals simp [initial, update, Config.overdue, counter, Some.one]

end Accordant

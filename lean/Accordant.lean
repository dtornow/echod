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

* `Event`: what a client observes, and when the system's clock moved. A
  trace's order is the order one observer saw.
* `Model`: the system, a state machine. It reads the clock (`now` is an
  argument) and never moves it.
* `Config`: the system at one point: the model's state, the external ops in
  flight, the internal ops scheduled, the dispatches in transit, the clock.
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
search itself needs no proof (though `Search.lean` proves one anyway).
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
  /-- The system's clock now reads `t`. Time is the system's own; a trace
      records when it moved. -/
  | clock (t : Time)

/-! ## The system -/

/-- An internal op to start, and when it runs, on the system's clock. -/
inductive Sched (I : Type) where
  | later (req : I)                  -- from now on, or never
  | timer (at_ : Time) (req : I)     -- at the given time

def Sched.req {I : Type} : Sched I → I
  | .later r => r
  | .timer _ r => r

/-- The time a timer is due; a `later` has none. -/
def Sched.due {I : Type} : Sched I → Option Time
  | .later _ => none
  | .timer t _ => some t

/-- Whether the op may run at `now`. -/
def Sched.Ready {I : Type} (now : Time) : Sched I → Prop
  | .later _ => True
  | .timer t _ => t ≤ now

/-- One possible effect of a request. -/
structure ExternalOutcome (S R I D : Type) where
  next : S
  resp : R
  work : List (Sched I)
  send : List D

/-- One possible effect of an internal op. -/
structure InternalOutcome (S I D : Type) where
  next : S
  work : List (Sched I)
  send : List D

/-- At least one. Nondeterminism is a list of alternatives; this is a list
    that can't be empty, so a request can't be refused. -/
abbrev Some (α : Type) := { xs : List α // xs ≠ [] }

/-- Exactly one. -/
def Some.one {α : Type} (x : α) : Some α := ⟨[x], by simp⟩

/-- The system: requests from clients, work it does on its own. It reads the
    clock and never moves it. -/
structure Model where
  State    : Type
  External : Type
  Response : Type
  Internal : Type
  Dispatch : Type
  /-- A request takes effect, at time `now`: every allowed outcome. At least
      one: every request is accepted in every state (input-enabled). -/
  external : External → State → Time → Some (ExternalOutcome State Response Internal Dispatch)
  /-- An internal op runs, at time `now`: every possible outcome. Empty: it
      can't run now. -/
  internal : Internal → State → Time → List (InternalOutcome State Internal Dispatch)
  /-- Responses can be compared: a client sees exactly the predicted one. -/
  decEq    : DecidableEq Response := by infer_instance
  /-- Dispatches can be compared: a client receives one by its value. -/
  decEqDispatch : DecidableEq Dispatch := by infer_instance

abbrev Model.Ev (m : Model) := Event m.External m.Response m.Dispatch

/-! ## Configurations: everything about the system at one point, seen or not -/

/-- An external op a client sent, until it returns. -/
structure ExternalOp (m : Model) where
  id  : CallId
  req : m.External
  res : Option m.Response   -- none while pending; some once settled

/-- The system at one point: the model's state, and what the model doesn't
    know about: the external ops in flight, the internal ops scheduled, the
    dispatches sent and not yet received, and the clock. -/
structure Config (m : Model) where
  state     : m.State
  externals : List (ExternalOp m)
  internals : List (Sched m.Internal)
  sent      : List m.Dispatch
  now       : Time              -- the model reads it, never moves it

/-- An internal op started at time `now`: a timer in the past fires now. -/
def schedule {I : Type} (now : Time) : Sched I → Sched I
  | .later r    => .later r
  | .timer t r  => .timer (max t now) r

variable {m : Model}

/-- A timer whose time has come and that can run. -/
def Config.Overdue (c : Config m) : Sched m.Internal → Prop
  | .later _ => False
  | .timer t r => t ≤ c.now ∧ m.internal r c.state c.now ≠ []

/-- Some internal op is overdue: it runs before anything else happens. -/
def Config.overdue (c : Config m) : Prop := ∃ w ∈ c.internals, c.Overdue w

/-- `w` is overdue with the earliest deadline: when the clock jumped past
    several deadlines, their ops run in deadline order. -/
def Config.First (c : Config m) (w : Sched m.Internal) : Prop :=
  c.Overdue w ∧ ∀ v ∈ c.internals, c.Overdue v → ∃ d e, w.due = some d ∧ v.due = some e ∧ d ≤ e

/-- No outstanding external op has this id. -/
def Config.Fresh (c : Config m) (id : CallId) : Prop := ∀ o ∈ c.externals, o.id ≠ id

/-! ## Steps: how the system evolves, and what each step shows a client -/

/-- Observed: a client sees an event. Silent: nothing shows. -/
inductive Label (m : Model) where
  | obs (e : m.Ev)
  | silent

inductive Step (m : Model) : Config m → Label m → Config m → Prop where
  /-- A client sends a request. Observed. -/
  | invoke {c : Config m} {id req} :
      c.Fresh id → ¬ c.overdue →
      Step m c (.obs (.invoke id req)) { c with externals := c.externals ++ [⟨id, req, none⟩] }
  /-- A client receives the response its call settled with. Observed. -/
  | ret {c : Config m} {pre post id req res} :
      c.externals = pre ++ ⟨id, req, some res⟩ :: post → ¬ c.overdue →
      Step m c (.obs (.ret id res)) { c with externals := pre ++ post }
  /-- A client receives a dispatch that was sent and not yet received. Observed. -/
  | receive {c : Config m} {pre post msg} :
      c.sent = pre ++ msg :: post → ¬ c.overdue →
      Step m c (.obs (.receive msg)) { c with sent := pre ++ post }
  /-- The clock moves forward. Observed: a trace records it. Timers due by the
      new time are then overdue, and run before anything else is observed. -/
  | clock {c : Config m} {t} :
      c.now ≤ t → ¬ c.overdue →
      Step m c (.obs (.clock t)) { c with now := t }
  /-- A pending external op settles with one of its allowed outcomes. The
      internal ops it starts are on the clock as it reads now. Silent. -/
  | effect {c : Config m} {pre post id req o} :
      c.externals = pre ++ ⟨id, req, none⟩ :: post →
      o ∈ (m.external req c.state c.now).val → ¬ c.overdue →
      Step m c .silent
        { c with state     := o.next
                 externals := pre ++ ⟨id, req, some o.resp⟩ :: post
                 internals := c.internals ++ o.work.map (schedule c.now)
                 sent      := c.sent ++ o.send }
  /-- An internal op whose time has come runs with one of its outcomes; while
      some op is overdue, only an overdue op with the earliest deadline runs.
      Silent. -/
  | run {c : Config m} {pre post w o} :
      c.internals = pre ++ w :: post → w.Ready c.now → o ∈ m.internal w.req c.state c.now →
      (c.overdue → c.First w) →
      Step m c .silent
        { c with state     := o.next
                 internals := pre ++ post ++ o.work.map (schedule c.now)
                 sent      := c.sent ++ o.send }

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

/-- The system starts in `init`, with nothing in flight, at time 0. -/
def initial (init : m.State) : Config m :=
  ⟨init, [], [], [], 0⟩

/-- The trace is valid: some execution of the system, from `initial init`,
    projected onto what clients observe, is exactly the trace. -/
def Valid (m : Model) (init : m.State) (trace : List m.Ev) : Prop :=
  ∃ steps, Legal m (initial init) steps ∧ project steps = trace

/-! ## Certificates: checking an execution someone found

Finding an execution is hard: the checker searches. Checking one is easy: walk
it, one step at a time. The trace already has the observed steps; a
certificate adds the silent ones the checker found, each naming which op and
which outcome. `replay` rebuilds the configurations and fails on the first step
the system can't make. -/

/-- A silent step, as a certificate names it. -/
inductive Silent where
  /-- The external op with this id settles with the `j`-th of its outcomes. -/
  | effect (call : CallId) (j : Nat)
  /-- The `i`-th internal op runs with the `j`-th of its outcomes. -/
  | run (i j : Nat)

/-- A certificate: for each event of the trace, the silent steps just before it. -/
abbrev Certificate := List (List Silent)

/-- One step of the replay: an event of the trace, or a silent step. -/
inductive Move (m : Model) where
  | obs (e : m.Ev)
  | silent (s : Silent)

/-- The first element satisfying `p`, with what is before and after it. -/
def splitAt? {α : Type} (p : α → Bool) : List α → Option (List α × α × List α)
  | [] => none
  | x :: xs => if p x then some ([], x, xs) else (splitAt? p xs).map fun (pre, y, post) => (x :: pre, y, post)

/-- `Overdue`, `overdue`, `Ready` and `First`, computed. -/
def Sched.isOverdue (c : Config m) : Sched m.Internal → Bool
  | .later _ => false
  | .timer t r => decide (t ≤ c.now) && !(m.internal r c.state c.now).isEmpty

def Config.isOverdue (c : Config m) : Bool := c.internals.any (Sched.isOverdue c)

def Sched.isReady {I : Type} (now : Time) : Sched I → Bool
  | .later _ => true
  | .timer t _ => decide (t ≤ now)

def dueLe {I : Type} (w v : Sched I) : Bool :=
  match w.due, v.due with
  | some d, some e => decide (d ≤ e)
  | _, _ => false

/-- Whether `w` may run: nothing is overdue, or `w` is overdue with the
    earliest deadline. -/
def Config.mayRun (c : Config m) (w : Sched m.Internal) : Bool :=
  !c.isOverdue || (w.isOverdue c && c.internals.all fun v => !v.isOverdue c || dueLe w v)

/-- The pending external op with this id. -/
def pendingOp (id : CallId) (o : ExternalOp m) : Bool := o.id == id && o.res.isNone

/-- The settled external op with this id and this response. -/
def settledOp (id : CallId) (res : m.Response) (o : ExternalOp m) : Bool :=
  o.id == id && match o.res with
    | some r => @decide (r = res) (m.decEq r res)
    | none => false

/-- One move from `c`: the step's label and where it leads, if the system can make it. -/
def Config.move (c : Config m) : Move m → Option (Label m × Config m)
  | .obs (.invoke id req) =>
      if c.externals.all (fun o => o.id != id) && !c.isOverdue then
        some (.obs (.invoke id req), { c with externals := c.externals ++ [⟨id, req, none⟩] })
      else none
  | .obs (.ret id res) =>
      match splitAt? (settledOp id res) c.externals with
      | some (pre, _, post) =>
          if !c.isOverdue then some (.obs (.ret id res), { c with externals := pre ++ post }) else none
      | none => none
  | .obs (.receive msg) =>
      match splitAt? (fun d => @decide (d = msg) (m.decEqDispatch d msg)) c.sent with
      | some (pre, _, post) =>
          if !c.isOverdue then some (.obs (.receive msg), { c with sent := pre ++ post }) else none
      | none => none
  | .obs (.clock t) =>
      if decide (c.now ≤ t) && !c.isOverdue then
        some (.obs (.clock t), { c with now := t })
      else none
  | .silent (.effect id j) =>
      match splitAt? (pendingOp id) c.externals with
      | some (pre, o, post) =>
          match (m.external o.req c.state c.now).val[j]? with
          | some out =>
              if !c.isOverdue then
                some (.silent, { c with state     := out.next
                                        externals := pre ++ { o with res := some out.resp } :: post
                                        internals := c.internals ++ out.work.map (schedule c.now)
                                        sent      := c.sent ++ out.send })
              else none
          | none => none
      | none => none
  | .silent (.run i j) =>
      match c.internals[i]? with
      | some w =>
          match (m.internal w.req c.state c.now)[j]? with
          | some out =>
              if w.isReady c.now && c.mayRun w then
                some (.silent, { c with state     := out.next
                                        internals := c.internals.take i ++ c.internals.drop (i + 1) ++
                                                       out.work.map (schedule c.now)
                                        sent      := c.sent ++ out.send })
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

/-! ### The computed tests agree with the defined ones -/

theorem isOverdue_iff {c : Config m} {w : Sched m.Internal} :
    w.isOverdue c = true ↔ c.Overdue w := by
  cases w <;> simp [Sched.isOverdue, Config.Overdue]

theorem isReady_iff {I : Type} {now : Time} {w : Sched I} :
    w.isReady now = true ↔ w.Ready now := by
  cases w <;> simp [Sched.isReady, Sched.Ready]

theorem not_overdue {c : Config m} (h : c.isOverdue = false) : ¬ c.overdue := by
  rintro ⟨w, hw, hov⟩
  have : c.isOverdue = true := List.any_eq_true.mpr ⟨w, hw, isOverdue_iff.mpr hov⟩
  simp_all

theorem may_run {c : Config m} {w : Sched m.Internal} (h : c.mayRun w = true) :
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

theorem splitAt?_spec {α : Type} {p : α → Bool} {l pre post : List α} {x : α}
    (h : splitAt? p l = some (pre, x, post)) : l = pre ++ x :: post ∧ p x = true := by
  induction l generalizing pre with
  | nil => simp [splitAt?] at h
  | cons y ys ih =>
    simp only [splitAt?] at h
    split at h
    · rename_i hy
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, hy⟩
    · obtain ⟨⟨pre', z, post'⟩, hz, he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      obtain ⟨h1, h2⟩ := ih hz
      exact ⟨by simp [h1], h2⟩

theorem move_step {c c' : Config m} {mv : Move m} {l : Label m}
    (h : c.move mv = some (l, c')) : Step m c l c' := by
  cases mv with
  | obs e =>
    cases e with
      | invoke id req =>
        simp only [Config.move] at h
        split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rename_i hc
        simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne, Bool.not_eq_true'] at hc
        exact .invoke hc.1 (not_overdue hc.2)
      | ret id res =>
        simp only [Config.move] at h
        split at h <;> try simp at h
        rename_i pre o post hsplit
        obtain ⟨ho, rfl, rfl⟩ := h
        obtain ⟨h1, h2⟩ := splitAt?_spec hsplit
        obtain ⟨oid, oreq, ores⟩ := o
        cases ores with
        | none => simp [settledOp] at h2
        | some r =>
          simp only [settledOp, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h2
          obtain ⟨rfl, rfl⟩ := h2
          exact .ret h1 (not_overdue ho)
      | receive msg =>
        simp only [Config.move] at h
        split at h <;> try simp at h
        rename_i pre d post hsplit
        obtain ⟨ho, rfl, rfl⟩ := h
        obtain ⟨h1, h2⟩ := splitAt?_spec hsplit
        have : d = msg := by simpa using h2
        subst this
        exact .receive h1 (not_overdue ho)
      | clock t =>
        simp only [Config.move] at h
        split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rename_i hc
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
        exact .clock hc.1 (not_overdue hc.2)
  | silent s =>
    cases s with
      | effect id j =>
        simp only [Config.move] at h
        split at h <;> try simp at h
        rename_i pre o post hsplit
        split at h <;> try simp at h
        rename_i out hout
        obtain ⟨ho, rfl, rfl⟩ := h
        obtain ⟨h1, h2⟩ := splitAt?_spec hsplit
        obtain ⟨oid, oreq, ores⟩ := o
        simp only [pendingOp, Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at h2
        obtain ⟨rfl, rfl⟩ := h2
        exact .effect h1 (List.mem_of_getElem? hout) (not_overdue ho)
      | run i j =>
        simp only [Config.move] at h
        split at h <;> try simp at h
        rename_i w hw
        split at h <;> try simp at h
        rename_i out hout
        obtain ⟨⟨ha, hc⟩, rfl, rfl⟩ := h
        rw [← List.append_assoc]
        exact .run (split_at hw) (isReady_iff.mp ha) (List.mem_of_getElem? hout) (may_run hc)

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
  external := fun _ n _ => .one ⟨n + 1, n + 1, [], []⟩
  internal := fun e _ _ => nomatch e

abbrev incr : ExternalOutcome Nat Nat Empty Empty := ⟨1, 1, [], []⟩

/-- Sent, then answered 1: valid. The execution is invoke (observed), effect
    (silent), return (observed). -/
example : Valid counter (0 : Nat) [.invoke 7 (), .ret 7 1] := by
  refine ⟨[(.obs (.invoke 7 ()), _), (.silent, _), (.obs (.ret 7 1), _)],
    ⟨.invoke ?_ ?_, .effect (pre := []) (post := []) (id := 7) (req := ()) (o := incr) ?_ ?_ ?_,
     .ret (pre := []) (post := []) (req := ()) ?_ ?_, trivial⟩, rfl⟩
  all_goals first
    | exact fun _ h => nomatch h
    | simp [initial, Config.overdue, counter, Some.one]

end Accordant

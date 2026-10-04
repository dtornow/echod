/-!
# The soundness statement of the accordant checker, in Lean

How the evolution of a system maps to what clients observe:

* The system is a labeled transition system over configurations.
* Every step either produces an observation (a request sent, a response
  received, a dispatch received) or is silent (a call taking effect, internal
  work running, time passing).
* A trace is valid when some sequence of steps from the start produces exactly
  those observations, in order, with any number of silent steps in between.

Everything is generic over the model: its types are fields of `Model`, and no
proof here looks inside them.

Not modeled yet: request lifetimes and `assert_idle`.
-/

namespace Accordant

abbrev Time := Nat
abbrev CallId := Nat

/-! ## Observations -/

/-- What a client observes, and when. -/
inductive Event (X R D : Type) where
  /-- The client sent a request. -/
  | invoke (time : Time) (call : CallId) (req : X)
  /-- The client got the response to that call. -/
  | ret (time : Time) (call : CallId) (res : R)
  /-- The client got a dispatch the server sent on its own. -/
  | receive (time : Time) (msg : D)

/-! ## The model -/

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
  external : External → State → Time → List (ExternalOutcome State Response Internal Dispatch)
  internal : Internal → State → Time → List (InternalOutcome State Internal Dispatch)

abbrev Model.Ev (m : Model) := Event m.External m.Response m.Dispatch

/-! ## Configurations: everything about a run at one point, seen or not -/

/-- A call the client has sent and not yet seen answered. -/
inductive Call (X R : Type) where
  | inFlight (req : X)   -- not yet taken effect
  | done (res : R)       -- taken effect; the client will see this response

/-- Internal work started and not yet run. -/
structure Work (I : Type) where
  req   : I
  after : Time          -- can't run before this
  due   : Option Time   -- must have run before anything is observed at or after this
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

/-- Time may move to `t` only if no work that can run is due before then. -/
def Config.mayAdvance (c : Config m) (t : Time) : Prop :=
  c.now < t ∧ ∀ w ∈ c.work, w.must = true → ∀ d, w.due = some d →
    m.internal w.req c.state c.now ≠ [] → t ≤ d

/-! ## Steps: how the system evolves, and what each step shows a client -/

/-- A step either shows a client an observation, or nothing. -/
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
  | ret {c : Config m} {call res} :
      c.calls call = some (.done res) → ¬ c.overdue →
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
  /-- Time passes, but not past a deadline whose work could still run. Silent. -/
  | advance {c : Config m} {t} :
      c.mayAdvance t → Step m c .silent { c with now := t }

/-- `Steps m c trace c'`: from `c`, some run reaches `c'` showing exactly `trace`. -/
inductive Steps (m : Model) : Config m → List m.Ev → Config m → Prop where
  | done {c} : Steps m c [] c
  | silent {c c' c'' trace} : Step m c .silent c' → Steps m c' trace c'' → Steps m c trace c''
  | obs {c c' c'' e trace} : Step m c (.obs e) c' → Steps m c' trace c'' → Steps m c (e :: trace) c''

def initial (init : m.State) (start : Time) : Config m :=
  ⟨init, start, fun _ => none, [], []⟩

/-- The trace is valid: some run of the model, from `init` at `start`, shows
    exactly these observations. -/
def Valid (m : Model) (init : m.State) (start : Time) (trace : List m.Ev) : Prop :=
  ∃ c, Steps m (initial init start) trace c

/-! ## The theorem -/

/-- The checker's verdict (Lean's `Accepted` in resonate-specification). -/
opaque Accepted (m : Model) (init : m.State) (start : Time) (trace : List m.Ev) : Prop

/-- Soundness: whatever the checker accepts is valid. Stated, not proved. -/
theorem accepted_implies_valid (m : Model) (init : m.State) (start : Time) (trace : List m.Ev)
    (_h : Accepted m init start trace) : Valid m init start trace := by
  sorry

/-! ## Sanity checks, proved -/

/-- For every model, the empty trace is valid. -/
theorem empty_trace_valid (m : Model) (init : m.State) (start : Time) :
    Valid m init start [] :=
  ⟨_, .done⟩

/-- A one-call counter: `incr` takes effect and answers the new value. -/
abbrev counter : Model where
  State    := Nat
  External := Unit
  Response := Nat
  Internal := Empty
  Dispatch := Empty
  external := fun _ n _ => [⟨n + 1, n + 1, [], []⟩]
  internal := fun e _ _ => nomatch e

/-- Sent at 0, answered 1 at 0: valid. The run is invoke (seen), effect
    (silent), return (seen). -/
example : Valid counter (0 : Nat) 0 [.invoke 0 7 (), .ret 0 7 1] := by
  refine ⟨_, .obs (.invoke ?_ ?_) (.silent (.effect (call := 7) (req := ()) (o := (⟨1, 1, [], []⟩ : ExternalOutcome counter.State counter.Response counter.Internal counter.Dispatch)) ?_ ?_ ?_) (.obs (.ret ?_ ?_) .done))⟩
  all_goals simp [initial, update, Config.overdue, counter]

end Accordant

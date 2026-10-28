import Experiment.Service

/-!
# Two templates: a process, and a process that calls

A **process** is what experiment 1 calls a `Service`: one step per
message. The shells, the checker and the proofs see only processes.

A **caller** is a process that may send a request and wait for its reply,
many at once. The author names the points where something waits, in a type
`Wait` of their own, with the data each needs, and writes two handlers:
`receive` for a message that is not a reply, and `resume` for the reply to
a call waiting at `w`. `call to req w` sends `req id` under a fresh id and
records that `id` waits at `w`.

`Caller.toService` turns a caller into a process. The bookkeeping is
there, once: the ids, the calls waiting, and matching a reply to its call
(by `replyTo`, which says which call a message answers). The state is
data: the author's, plus the calls waiting. Nothing in it is a function.

Proved here, for every caller whose handlers are built from this file's
operations (`Keeps`):

* **routing** (`step_reply`, `step_other`): a reply to a waiting call runs
  `resume` on that call, with the call no longer waiting; anything else
  runs `receive`;
* **fresh ids** (`fresh_step`): every waiting id is below the next id;
* **at most once** (`once`): after a call is resumed, its id is not
  waiting any more, whatever the handler did.
-/

namespace Exp3

open Experiment (Time Addr Some Out Service)

/-- The author's state, and the calls waiting, by id. -/
structure Calls (S W : Type) where
  data    : S
  waiting : List (Nat × W) := []
  next    : Nat := 0

/-- A caller's handler: like experiment 1's, over the author's state, with
    calls. -/
def C (E S W M α : Type) : Type := E → Calls S W → Some (α × Calls S W × List (Out M))

variable {E S W M : Type}

instance : Monad (C E S W M) where
  pure a := fun _ s => .one (a, s, [])
  bind x f := fun e s =>
    (x e s).bind fun (a, s₁, w₁) => (f a e s₁).map fun (b, s₂, w₂) => (b, s₂, w₁ ++ w₂)

instance : MonadReaderOf E (C E S W M) where
  read := fun e s => .one (e, s, [])

/-- `get`, `set` and `modify` see the author's state only. -/
instance : MonadStateOf S (C E S W M) where
  get := fun _ s => .one (s.data, s, [])
  set d := fun _ s => .one ((), { s with data := d }, [])
  modifyGet f := fun _ s => let (a, d) := f s.data; .one (a, { s with data := d }, [])

namespace C

def emit (o : Out M) : C E S W M Unit := fun _ s => .one ((), s, [o])

def send (to : Addr) (m : M) : C E S W M Unit := emit (.send to m)

def choose {α : Type} (xs : Some α) : C E S W M α := fun _ s => xs.map (·, s, [])

/-- Send `req id` to `to` under a fresh `id`, and wait at `w` for the reply. -/
def call (to : Addr) (req : Nat → M) (w : W) : C E S W M Unit := fun _ s =>
  .one ((), { s with waiting := (s.next, w) :: s.waiting, next := s.next + 1 }, [.send to (req s.next)])

end C

/-- A process that calls. -/
structure Caller where
  Config  : Type
  State   : Type
  Msg     : Type
  Wait    : Type
  /-- Which call a message answers, if it is a reply. -/
  replyTo : Msg → Option Nat
  /-- A message that is not a reply to a waiting call. -/
  receive : Addr → Msg → Time → C Config State Wait Msg Unit
  /-- The reply to the call waiting at `w`. -/
  resume  : Wait → Addr → Msg → Time → C Config State Wait Msg Unit

/-- The call `m` answers, if it is waiting. -/
def waitingFor {W M : Type} (replyTo : M → Option Nat) (s : Calls S W) (m : M) : Option (Nat × W) :=
  (replyTo m).bind fun id => (s.waiting.find? (·.1 == id)).map fun p => (id, p.2)

def Calls.drop {W : Type} (s : Calls S W) (id : Nat) : Calls S W :=
  { s with waiting := s.waiting.filter (·.1 != id) }

/-- One step of the caller on a message. -/
def Caller.step (c : Caller) (sender : Addr) (m : c.Msg) (now : Time) :
    C c.Config c.State c.Wait c.Msg Unit := fun e s =>
  match waitingFor c.replyTo s m with
  | some (id, w) => c.resume w sender m now e (s.drop id)
  | none => c.receive sender m now e s

/-- The caller as a process. -/
def Caller.toService (c : Caller) : Service where
  Config  := c.Config
  State   := Calls c.State c.Wait
  Msg     := c.Msg
  receive := c.step
  tick    := fun _ _ s => .one ((), s, [])

/-! ## Routing -/

theorem step_reply (c : Caller) {s : Calls c.State c.Wait} {m : c.Msg} {id : Nat} {w : c.Wait}
    (h : waitingFor c.replyTo s m = some (id, w)) (sender : Addr) (now : Time) (e : c.Config) :
    c.step sender m now e s = c.resume w sender m now e (s.drop id) := by
  simp [Caller.step, h]

theorem step_other (c : Caller) {s : Calls c.State c.Wait} {m : c.Msg}
    (h : waitingFor c.replyTo s m = none) (sender : Addr) (now : Time) (e : c.Config) :
    c.step sender m now e s = c.receive sender m now e s := by
  simp [Caller.step, h]

/-! ## The calls waiting only grow by fresh calls -/

/-- From `s` to `s'`: the next id never goes back, and every call waiting
    in `s'` was waiting in `s` or was made in between. -/
def Mono {W : Type} (s s' : Calls S W) : Prop :=
  s.next ≤ s'.next ∧ ∀ p ∈ s'.waiting, p ∈ s.waiting ∨ (s.next ≤ p.1 ∧ p.1 < s'.next)

theorem Mono.refl {W : Type} (s : Calls S W) : Mono s s := ⟨Nat.le_refl _, fun _ h => .inl h⟩

theorem Mono.trans {W : Type} {s₁ s₂ s₃ : Calls S W} (h₁ : Mono s₁ s₂) (h₂ : Mono s₂ s₃) :
    Mono s₁ s₃ := by
  refine ⟨Nat.le_trans h₁.1 h₂.1, fun p hp => ?_⟩
  rcases h₂.2 p hp with hp | ⟨l, u⟩
  · rcases h₁.2 p hp with hp | ⟨l', u'⟩
    · exact .inl hp
    · exact .inr ⟨l', Nat.lt_of_lt_of_le u' h₂.1⟩
  · exact .inr ⟨Nat.le_trans h₁.1 l, u⟩

/-- A handler that changes the calls waiting only by making calls. -/
def Keeps {α : Type} (x : C E S W M α) : Prop :=
  ∀ e s, ∀ r ∈ (x e s).val, Mono s r.2.1

theorem Keeps.pure {α : Type} (a : α) : Keeps (pure a : C E S W M α) := by
  intro e s r hr
  simp [Pure.pure, Some.one] at hr
  subst hr; exact Mono.refl _

theorem Keeps.bind {α β : Type} {x : C E S W M α} {f : α → C E S W M β}
    (hx : Keeps x) (hf : ∀ a, Keeps (f a)) : Keeps (x >>= f) := by
  intro e s r hr
  simp only [Bind.bind, Some.bind, Some.map, List.mem_flatMap, List.mem_map] at hr
  obtain ⟨⟨a, s₁, w₁⟩, h₁, ⟨b, s₂, w₂⟩, h₂, rfl⟩ := hr
  exact (hx e s _ h₁).trans (hf a e s₁ (b, s₂, w₂) h₂)

theorem Keeps.read : Keeps (read : C E S W M E) := by
  intro e s r hr
  change r ∈ [(e, s, [])] at hr
  simp at hr
  subst hr; exact Mono.refl _

theorem Keeps.get : Keeps (get : C E S W M S) := by
  intro e s r hr
  change r ∈ [(s.data, s, [])] at hr
  simp at hr
  subst hr; exact Mono.refl _

theorem Keeps.set (d : S) : Keeps (set d : C E S W M Unit) := by
  intro e s r hr
  change r ∈ [((), { s with data := d }, [])] at hr
  simp at hr
  subst hr; exact ⟨Nat.le_refl _, fun p h => .inl h⟩

theorem Keeps.emit (o : Out M) : Keeps (C.emit o : C E S W M Unit) := by
  intro e s r hr
  simp [C.emit, Some.one] at hr
  subst hr; exact Mono.refl _

theorem Keeps.send (to : Addr) (m : M) : Keeps (C.send to m : C E S W M Unit) := Keeps.emit _

theorem Keeps.choose {α : Type} (xs : Some α) : Keeps (C.choose xs : C E S W M α) := by
  intro e s r hr
  simp [C.choose, Some.map] at hr
  obtain ⟨a, _, rfl⟩ := hr
  exact Mono.refl _

theorem Keeps.call (to : Addr) (req : Nat → M) (w : W) : Keeps (C.call to req w : C E S W M Unit) := by
  intro e s r hr
  simp [C.call, Some.one] at hr
  subst hr
  refine ⟨Nat.le_succ _, fun p hp => ?_⟩
  simp only [List.mem_cons] at hp
  rcases hp with rfl | hp
  · exact .inr ⟨Nat.le_refl _, Nat.lt_succ_self _⟩
  · exact .inl hp

/-! ## Fresh ids, and at most once -/

/-- Every waiting id is below the next one. -/
def Fresh {W : Type} (s : Calls S W) : Prop := ∀ p ∈ s.waiting, p.1 < s.next

theorem Fresh.mono {W : Type} {s s' : Calls S W} (h : Fresh s) (hm : Mono s s') : Fresh s' := by
  intro p hp
  rcases hm.2 p hp with hp | ⟨_, u⟩
  · exact Nat.lt_of_lt_of_le (h p hp) hm.1
  · exact u

/-- A caller whose handlers keep the calls waiting. -/
def Caller.Keeps (c : Caller) : Prop :=
  (∀ sender m now, Exp3.Keeps (c.receive sender m now)) ∧
  (∀ w sender m now, Exp3.Keeps (c.resume w sender m now))

theorem drop_mono {W : Type} (s : Calls S W) (id : Nat) : Mono s (s.drop id) :=
  ⟨Nat.le_refl _, fun _ hp => .inl (List.mem_filter.mp hp).1⟩

/-- **Fresh ids**: a step keeps every waiting id below the next. -/
theorem fresh_step {c : Caller} (hc : c.Keeps) {s : Calls c.State c.Wait} (hs : Fresh s)
    (sender : Addr) (m : c.Msg) (now : Time) (e : c.Config) :
    ∀ r ∈ (c.step sender m now e s).val, Fresh r.2.1 := by
  intro r hr
  cases h : waitingFor c.replyTo s m with
  | none =>
    rw [step_other c h] at hr
    exact hs.mono (hc.1 sender m now e s r hr)
  | some idw =>
    obtain ⟨id, w⟩ := idw
    rw [step_reply c h] at hr
    exact hs.mono ((drop_mono s id).trans (hc.2 w sender m now e _ r hr))

/-- **At most once**: once the call `id` is resumed, it is not waiting any
    more, whatever the handler did: the calls it made are new. -/
theorem once {c : Caller} (hc : c.Keeps) {s : Calls c.State c.Wait} (hs : Fresh s)
    {m : c.Msg} {id : Nat} {w : c.Wait} (h : waitingFor c.replyTo s m = some (id, w))
    (sender : Addr) (now : Time) (e : c.Config) :
    ∀ r ∈ (c.step sender m now e s).val, ∀ w', (id, w') ∉ r.2.1.waiting := by
  intro r hr w' hin
  rw [step_reply c h] at hr
  have hid : ∃ w₀, (id, w₀) ∈ s.waiting := by
    simp only [waitingFor, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨id', hrep, ⟨id₀, w₀⟩, hfind, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have := List.find?_some hfind
    simp only [beq_iff_eq] at this
    subst this
    exact ⟨w₀, List.mem_of_find?_eq_some hfind⟩
  obtain ⟨w₀, hw₀⟩ := hid
  rcases (hc.2 w sender m now e _ r hr).2 _ hin with hd | ⟨l, _⟩
  · simp [Calls.drop] at hd
  · exact absurd (hs _ hw₀) (Nat.not_lt.mpr l)

end Exp3

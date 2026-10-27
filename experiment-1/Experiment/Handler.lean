/-!
# The handler monad, from scratch

A handler reads an environment `E`, updates a state `S`, emits `W`s, and
may **choose**: where the specification allows more than one behavior, a
handler says so with `choose`, and running it gives every outcome.

* **read** the environment: configuration, such as default timeouts, so
  no number in a handler is magic;
* **update** the state, and see its own writes: a handler is ordinary
  sequential code;
* **emit**: messages, and assertions for fuzzing. Emitting is write-only:
  a handler can never read back what it emitted, so an assertion cannot
  change what it does;
* **choose** among the behaviors the specification allows. Never among
  none: `choose` takes a nonempty list, so a handler always has at least
  one outcome, and that is in its type.

Time is not in the environment: handlers take `now` as a parameter.
-/

namespace Experiment

abbrev Time := Nat
abbrev Addr := String

/-- At least one. -/
abbrev Some (α : Type) := { xs : List α // xs ≠ [] }

def Some.one {α : Type} (x : α) : Some α := ⟨[x], by simp⟩

def Some.map {α β : Type} (f : α → β) (xs : Some α) : Some β :=
  ⟨xs.val.map f, by simpa using xs.property⟩

def Some.bind {α β : Type} (xs : Some α) (f : α → Some β) : Some β :=
  ⟨xs.val.flatMap fun a => (f a).val, by
    obtain ⟨xs, h⟩ := xs
    cases xs with
    | nil => contradiction
    | cons a _ => simp [(f a).property]⟩

/-- A handler: given the environment and the state, every allowed outcome:
    a result, the next state, and what it emitted. -/
def H (E S W α : Type) : Type := E → S → Some (α × S × List W)

variable {E S W : Type}

instance : Monad (H E S W) where
  pure a   := fun _ s => .one (a, s, [])
  bind x f := fun e s =>
    (x e s).bind fun (a, s₁, w₁) =>                 -- every outcome of the first part,
      (f a e s₁).map fun (b, s₂, w₂) => (b, s₂, w₁ ++ w₂)   -- the rest from its state

/-- `read` gives the environment. -/
instance : MonadReaderOf E (H E S W) where
  read := fun e s => .one (e, s, [])

/-- `get`, `set` and `modify` work on the state. -/
instance : MonadStateOf S (H E S W) where
  get := fun _ s => .one (s, s, [])
  set s := fun _ _ => .one ((), s, [])
  modifyGet f := fun _ s => let (a, s') := f s; .one (a, s', [])

def emit (w : W) : H E S W Unit := fun _ s => .one ((), s, [w])

/-- Any of these: the specification allows each. -/
def choose {α : Type} (xs : Some α) : H E S W α := fun _ s => xs.map (·, s, [])

def H.run {α : Type} (x : H E S W α) (e : E) (s : S) : Some (α × S × List W) := x e s

/-! ## What handlers emit -/

/-- A message to send, or an assertion. -/
inductive Out (M : Type) where
  | send      (to : Addr) (m : M)
  /-- Must hold every time it is emitted. -/
  | always    (name : String) (ok : Bool)
  /-- Should hold at least once, over a fuzzing run. -/
  | sometimes (name : String) (hit : Bool)
  deriving DecidableEq, Repr

def sends {M : Type} (outs : List (Out M)) : List (Addr × M) :=
  outs.filterMap fun | .send a m => some (a, m) | _ => none

def failed {M : Type} (outs : List (Out M)) : List String :=
  outs.filterMap fun | .always n false => some n | _ => none

def hit {M : Type} (outs : List (Out M)) : List String :=
  outs.filterMap fun | .sometimes n true => some n | _ => none

end Experiment

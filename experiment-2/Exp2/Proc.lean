import Experiment.Service

/-!
# Processes as code, after Lynx

Lynx (josevalim/lynx) models an Erlang process as a resumable computation:
an inductive whose constructors are the process's requests to the runtime
(`get`, `set`, `send`, `receive`, `schedule` for spawn), each holding the
continuation. Code is written as ordinary sequential code in its monad; a
scheduler runs the continuations.

This is that idea, cut to what our step functions have, plus what they
have that Lynx does not:

* `ask`, `load`, `store`, `emit`: our handler monad's four operations,
  read, get, set and emit (`emit` covers sends and assertions alike);
* `choose`: the specification's nondeterminism (Lynx has none inside a
  process; its only choice is the scheduler's);
* `receive`: Erlang's selective receive, as in Lynx: the oldest message in
  the mailbox the pattern accepts, the rest left in place. It also hands
  over the instant, since our steps have one.

No spawn: our world has a fixed set of processes (see the README).

`toStep` turns such a process into a step function, the `receive` of a
`Service`: a message joins the mailbox, then the process runs from where
it was blocked until it blocks again. When the code ends, it starts over,
as an Erlang server loop does. So a process's state is its data, its
mailbox, and where it is blocked: the continuation.
-/

namespace Exp2

open Experiment (Time Addr Some Out Service H)

/-- A process as code. -/
inductive Proc (E S M : Type) (α : Type) where
  | pure (a : α)
  | ask (k : E → Proc E S M α)
  | load (k : S → Proc E S M α)
  | store (s : S) (k : Proc E S M α)
  | emit (o : Out M) (k : Proc E S M α)
  | emitMany (outs : List (Out M)) (k : Proc E S M α)
  /-- One of `n + 1` ways: never none. -/
  | choose (n : Nat) (k : Fin (n + 1) → Proc E S M α)
  /-- Block until a message `accept` takes is in the mailbox. -/
  | receive (accept : Addr → M → Bool) (k : Addr → M → Time → Proc E S M α)

namespace Proc

variable {E S M : Type}

def bind {α β : Type} : Proc E S M α → (α → Proc E S M β) → Proc E S M β
  | .pure a, f => f a
  | .ask k, f => .ask fun e => (k e).bind f
  | .load k, f => .load fun s => (k s).bind f
  | .store s k, f => .store s (k.bind f)
  | .emit o k, f => .emit o (k.bind f)
  | .emitMany outs k, f => .emitMany outs (k.bind f)
  | .choose n k, f => .choose n fun i => (k i).bind f
  | .receive acc k, f => .receive acc fun a m t => (k a m t).bind f

instance : Monad (Proc E S M) where
  pure := .pure
  bind := bind

instance : MonadReaderOf E (Proc E S M) where
  read := .ask .pure

instance : MonadStateOf S (Proc E S M) where
  get := .load .pure
  set s := .store s (.pure ())
  modifyGet f := .load fun s => let (a, s') := f s; .store s' (.pure a)

def send (to : Addr) (m : M) : Proc E S M Unit := .emit (.send to m) (.pure ())

def always (name : String) (ok : Bool) : Proc E S M Unit := .emit (.always name ok) (.pure ())

def emitAllNow (outs : List (Out M)) : Proc E S M Unit := .emitMany outs (.pure ())

/-- The oldest message `accept` takes: who sent it, what, and when it is taken. -/
def recv (accept : Addr → M → Bool) : Proc E S M (Addr × M × Time) :=
  .receive accept fun a m t => .pure (a, m, t)

/-- Any of these. -/
def oneOf {α : Type} : Some α → Proc E S M α
  | ⟨x :: rest, _⟩ => .choose rest.length fun i => .pure ((x :: rest)[i.val]'(by simp))
  | ⟨[], h⟩ => absurd rfl h

/-- Emit each output in order. -/
def emitAll : List (Out M) → Proc E S M Unit
  | [] => .pure ()
  | o :: rest => .emit o (emitAll rest)

end Proc

open Proc in
/-- A handler of our first monad, run as part of a process: any of its
    outcomes, its state written back, what it emitted emitted. -/
def Proc.lift {α : Type} (h : H E S (Out M) α) : Proc E S M α := do
  let (a, s, outs) ← oneOf (h (← read) (← get))
  set s
  emitAll outs
  return a


/-! ## From code to a step function -/

/-- A process at rest: its data, its mailbox, where it is blocked. -/
structure Running (E S M : Type) where
  data    : S
  mailbox : List (Addr × M) := []
  k       : Proc E S M Unit

/-- The first message `accept` takes, and the mailbox without it. -/
def take? {M : Type} (accept : Addr → M → Bool) : List (Addr × M) → Option (Addr × M × List (Addr × M))
  | [] => none
  | (a, m) :: rest =>
    if accept a m then some (a, m, rest)
    else (take? accept rest).map fun (a', m', rest') => (a', m', (a, m) :: rest')

theorem take?_append_match {M : Type} {accept : Addr → M → Bool}
    {mb : List (Addr × M)} {a : Addr} {m : M}
    (hn : take? accept mb = none) (ha : accept a m = true) :
    take? accept (mb ++ [(a, m)]) = some (a, m, mb) := by
  induction mb with
  | nil => simp [take?, ha]
  | cons x rest ih =>
    obtain ⟨b, n⟩ := x
    simp only [take?] at hn ⊢
    split at hn
    · simp at hn
    · rename_i hx
      cases hr : take? accept rest with
      | none =>
        simp only [hr, Option.map_none] at hn
        change take? accept ((b, n) :: (rest ++ [(a, m)])) =
          some (a, m, (b, n) :: rest)
        rw [take?.eq_def]
        simp only [hx]
        rw [ih hr]
        rfl
      | some result =>
        simp [hr] at hn

theorem take?_append_miss {M : Type} {accept : Addr → M → Bool}
    {mb : List (Addr × M)} {a : Addr} {m : M}
    (hn : take? accept mb = none) (ha : accept a m = false) :
    take? accept (mb ++ [(a, m)]) = none := by
  induction mb with
  | nil => simp [take?, ha]
  | cons x rest ih =>
    obtain ⟨b, n⟩ := x
    simp only [take?] at hn ⊢
    split at hn
    · simp at hn
    · rename_i hx
      cases hr : take? accept rest with
      | none =>
        simp only [hr, Option.map_none] at hn
        change take? accept ((b, n) :: (rest ++ [(a, m)])) = none
        rw [take?.eq_def]
        simp only [hx]
        rw [ih hr]
        rfl
      | some result =>
        simp [hr] at hn

variable {E S M : Type}

/-- Run from `k` until blocked, at `now`: every outcome, with what was
    emitted. When the code ends it starts over at `main`. `fuel` bounds the
    steps, for code that never blocks. -/
def advance (main : Proc E S M Unit) (e : E) (now : Time) :
    Nat → S → List (Addr × M) → Proc E S M Unit → List (Running E S M × List (Out M))
  | 0, s, mb, k => [(⟨s, mb, k⟩, [])]
  | fuel + 1, s, mb, k =>
    match k with
    | .pure () => advance main e now fuel s mb main
    | .ask k => advance main e now fuel s mb (k e)
    | .load k => advance main e now fuel s mb (k s)
    | .store s' k => advance main e now fuel s' mb k
    | .emit o k => (advance main e now fuel s mb k).map fun (r, os) => (r, o :: os)
    | .emitMany outs k => (advance main e now fuel s mb k).map fun (r, os) => (r, outs ++ os)
    | .choose n k => (List.finRange (n + 1)).flatMap fun i => advance main e now fuel s mb (k i)
    | .receive acc k =>
      match take? acc mb with
      | some (a, m, rest) => advance main e now fuel s rest (k a m now)
      | none => [(⟨s, mb, .receive acc k⟩, [])]

/-- A list we know is never empty, as one; `d` if it were. -/
def someOr {α : Type} (xs : List α) (d : α) : Some α :=
  match xs with
  | [] => .one d
  | x :: rest => ⟨x :: rest, by simp⟩

/-- The process's step on a message: into the mailbox, then run. -/
def toStep (main : Proc E S M Unit) (fuel : Nat := 1000) (sender : Addr) (m : M) (now : Time) :
    H E (Running E S M) (Out M) Unit := fun e r =>
  someOr ((advance main e now fuel r.data (r.mailbox ++ [(sender, m)]) r.k).map
    fun (r', outs) => ((), r', outs)) ((), r, [])

end Exp2

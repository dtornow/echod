import Exp2.Proc

/-!
# Refinement of experiment 1's handlers

`Proc` adds suspension to experiment 1's handler language.  On the common
fragment, its operations have exactly the old meaning.  This file states that
claim as a small-step-independent terminating evaluation relation and proves
it for `Proc.lift`, the embedding of an experiment 1 handler.

The two directions matter: lifting introduces neither new outcomes
(`lift_refines`) nor loses an outcome (`lift_complete`).
-/

namespace Exp2

open Experiment (H Out Some)

/-- A finite process computation that returns without reaching `receive`.
The relation records the initial and final data and the emitted outputs. -/
inductive Eval (e : E) : {α : Type} → S → Proc E S M α → α → S → List (Out M) → Prop where
  | pure {s : S} {a : α} : Eval e s (.pure a) a s []
  | ask {s : S} {k : E → Proc E S M α} {a : α} {s' : S} {outs : List (Out M)}
      (h : Eval e s (k e) a s' outs) : Eval e s (.ask k) a s' outs
  | load {s : S} {k : S → Proc E S M α} {a : α} {s' : S} {outs : List (Out M)}
      (h : Eval e s (k s) a s' outs) : Eval e s (.load k) a s' outs
  | store {s s₁ : S} {k : Proc E S M α} {a : α} {s' : S} {outs : List (Out M)}
      (h : Eval e s₁ k a s' outs) : Eval e s (.store s₁ k) a s' outs
  | emit {s : S} {o : Out M} {k : Proc E S M α} {a : α} {s' : S}
      {outs : List (Out M)} (h : Eval e s k a s' outs) :
      Eval e s (.emit o k) a s' (o :: outs)
  | emitMany {s : S} {batch : List (Out M)} {k : Proc E S M α} {a : α} {s' : S}
      {outs : List (Out M)} (h : Eval e s k a s' outs) :
      Eval e s (.emitMany batch k) a s' (batch ++ outs)
  | choose {s : S} {n : Nat} {k : Fin (n + 1) → Proc E S M α} {i : Fin (n + 1)}
      {a : α} {s' : S} {outs : List (Out M)} (h : Eval e s (k i) a s' outs) :
      Eval e s (.choose n k) a s' outs

namespace Eval

theorem bind {x : Proc E S M α} {f : α → Proc E S M β}
    (hx : Eval e s x a s₁ w₁) (hf : Eval e s₁ (f a) b s₂ w₂) :
    Eval e s (x >>= f) b s₂ (w₁ ++ w₂) := by
  induction hx generalizing β b with
  | pure =>
    change Eval e _ (f _) _ _ _
    exact hf
  | ask _ ih => exact .ask (ih hf)
  | load _ ih => exact .load (ih hf)
  | store _ ih => exact .store (ih hf)
  | emit _ ih => exact .emit (ih hf)
  | emitMany _ ih =>
    change Eval e _ (.emitMany _ (_ >>= f)) _ _ _
    simpa [List.append_assoc] using Eval.emitMany (ih hf)
  | choose _ ih => exact .choose (ih hf)

theorem bind_inv {x : Proc E S M α} {f : α → Proc E S M β}
    (h : Eval e s (x >>= f) b s₂ outs) :
    ∃ a s₁ w₁ w₂, Eval e s x a s₁ w₁ ∧ Eval e s₁ (f a) b s₂ w₂ ∧ outs = w₁ ++ w₂ := by
  induction x generalizing s b s₂ outs with
  | pure a =>
    exact ⟨a, s, [], outs, .pure, h, by simp⟩
  | ask k ih =>
    cases h with
    | ask h =>
      obtain ⟨a, s₁, w₁, w₂, hx, hf, rfl⟩ := ih _ h
      exact ⟨a, s₁, w₁, w₂, .ask hx, hf, rfl⟩
  | load k ih =>
    cases h with
    | load h =>
      obtain ⟨a, s₁, w₁, w₂, hx, hf, rfl⟩ := ih _ h
      exact ⟨a, s₁, w₁, w₂, .load hx, hf, rfl⟩
  | store s' k ih =>
    cases h with
    | store h =>
      obtain ⟨a, s₁, w₁, w₂, hx, hf, rfl⟩ := ih h
      exact ⟨a, s₁, w₁, w₂, .store hx, hf, rfl⟩
  | emit o k ih =>
    cases h with
    | emit h =>
      obtain ⟨a, s₁, w₁, w₂, hx, hf, rfl⟩ := ih h
      exact ⟨a, s₁, o :: w₁, w₂, .emit hx, hf, rfl⟩
  | emitMany batch k ih =>
    cases h with
    | emitMany h =>
      obtain ⟨a, s₁, w₁, w₂, hx, hf, rfl⟩ := ih h
      exact ⟨a, s₁, batch ++ w₁, w₂, .emitMany hx, hf, by simp⟩
  | choose n k ih =>
    cases h with
    | choose h =>
      obtain ⟨a, s₁, w₁, w₂, hx, hf, rfl⟩ := ih _ h
      exact ⟨a, s₁, w₁, w₂, .choose hx, hf, rfl⟩
  | receive accept k =>
    cases h

theorem read (e : E) (s : S) : Eval e s (read : Proc E S M E) e s [] :=
  .ask .pure

theorem get (e : E) (s : S) : Eval e s (get : Proc E S M S) s s [] :=
  .load .pure

theorem set (e : E) (s s' : S) : Eval e s (set s' : Proc E S M Unit) () s' [] :=
  .store .pure

theorem emits (e : E) (s : S) : ∀ outs : List (Out M),
    Eval e s (Proc.emitAll outs) () s outs := by
  intro outs
  induction outs with
  | nil => exact .pure
  | cons o rest ih => exact .emit ih

theorem emitAll_return_refines {xs : List (Out M)}
    (h : Eval e s (Proc.emitAll xs >>= fun _ => Proc.pure a) b s' outs) :
    b = a ∧ s' = s ∧ outs = xs := by
  induction xs generalizing b s' outs with
  | nil =>
    cases h with
    | pure => exact ⟨rfl, rfl, rfl⟩
  | cons o rest ih =>
    cases h with
    | emit h =>
      obtain ⟨rfl, rfl, rfl⟩ := ih h
      exact ⟨rfl, rfl, rfl⟩

theorem emitAll_return (e : E) (s : S) (xs : List (Out M)) (a : α) :
    Eval e s (Proc.emitAll xs >>= fun _ => Proc.pure a) a s xs := by
  induction xs with
  | nil => exact .pure
  | cons o rest ih => exact .emit ih

end Eval

/-- Every result selected by `oneOf` is one of its inputs. -/
theorem oneOf_refines {E S M α : Type} {e : E} {s s' : S} {a : α}
    {outs : List (Out M)} {xs : Some α}
    (h : Eval e s (@Proc.oneOf E S M α xs) a s' outs) :
    a ∈ xs.val ∧ s' = s ∧ outs = [] := by
  rcases xs with ⟨xs, hn⟩
  cases xs with
  | nil => contradiction
  | cons x rest =>
    cases h with
    | choose h =>
      cases h with
      | pure => exact ⟨List.getElem_mem .., rfl, rfl⟩

/-- Every input to `oneOf` can be selected. -/
theorem oneOf_complete {E S M α : Type} {e : E} {s : S} {a : α} {xs : Some α}
    (h : a ∈ xs.val) : Eval e s (@Proc.oneOf E S M α xs) a s [] := by
  rcases xs with ⟨xs, hn⟩
  cases xs with
  | nil => contradiction
  | cons x rest =>
    obtain ⟨i, hi⟩ := List.get_of_mem h
    rw [List.get_eq_getElem] at hi
    let j : Fin (rest.length + 1) := ⟨i.val, by
      change i.val < (x :: rest).length
      exact i.isLt⟩
    apply Eval.choose (i := j)
    have hj : (x :: rest)[j.val]'(by simp) = a := by simpa [j] using hi
    rw [hj]
    exact .pure

/-- Lifting an experiment 1 handler introduces no behavior. -/
theorem lift_refines {h : H E S (Out M) α}
    (hr : Eval e s (Proc.lift h) a s' outs) :
    (a, s', outs) ∈ (h e s).val := by
  unfold Proc.lift at hr
  cases hr with
  | ask hr =>
    cases hr with
    | load hr =>
      change Eval e s
        (Proc.oneOf (h e s) >>= fun r =>
          set r.2.1 >>= fun _ => Proc.emitAll r.2.2 >>= fun _ => Proc.pure r.1)
        a s' outs at hr
      obtain ⟨r, s₁, w₁, w₂, hone, hrest, hout⟩ := Eval.bind_inv hr
      obtain ⟨hmem, rfl, rfl⟩ := oneOf_refines hone
      subst outs
      rcases r with ⟨result, next, emitted⟩
      cases hrest with
      | store hrest =>
        obtain ⟨rfl, rfl, rfl⟩ := Eval.emitAll_return_refines hrest
        simpa using hmem

/-- Lifting preserves every behavior of an experiment 1 handler. -/
theorem lift_complete {h : H E S (Out M) α}
    (hr : (a, s', outs) ∈ (h e s).val) :
    Eval e s (Proc.lift h) a s' outs := by
  unfold Proc.lift
  apply Eval.ask
  apply Eval.load
  change Eval e s
    (Proc.oneOf (h e s) >>= fun r =>
      set r.2.1 >>= fun _ => Proc.emitAll r.2.2 >>= fun _ => Proc.pure r.1)
    a s' outs
  apply Eval.bind (oneOf_complete hr)
  apply Eval.store
  exact Eval.emitAll_return e s' outs a

/-- `Proc.lift` is an exact embedding of experiment 1's handler semantics. -/
theorem eval_lift_iff {h : H E S (Out M) α} :
    Eval e s (Proc.lift h) a s' outs ↔ (a, s', outs) ∈ (h e s).val :=
  ⟨lift_refines, lift_complete⟩

end Exp2

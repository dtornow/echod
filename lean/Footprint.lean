import Accordant

/-!
# Footprints: what an op touches, and what that buys

A footprint says which keys of the state an op may read or write. Its
meaning, the thing a checker can use, is that ops on disjoint keys commute:
taking `a` then `b` comes out the same as `b` then `a`, outcome for outcome.
That is what lets a search explore one order instead of both, and what lets
a system shard, lock or partition by key.

This file defines

* `Footprint m`: the declaration, a read set and a write set per op, and the
  conditions a model proves so the declaration is true. They are structural:
  the state is seen through a `view` per key; the keys cover the state
  (`complete`); an op's outcomes depend only on the views at its read set
  (`r_only`), and change no view outside its write set (`w_only`).
* `Footprint.commute`: from those conditions, independent ops commute, under
  Bernstein's condition: neither writes what the other reads or writes.
  Proved once, for every model.

A model author declares the sets and proves `r_only` and `w_only`, both about
which fields an op reads and writes. Commutation, an interleaving argument,
they never write. `bank` at the bottom is an instance.
-/

namespace Accordant

variable {m : Model}

/-! ## Ops and outcomes, uniformly -/

/-- An outcome of either kind of op. -/
structure Outcome (m : Model) where
  next : m.State
  resp : Option m.Response   -- some for a request, none for an internal op
  work : List (Sched m.Internal)
  send : List m.Dispatch

/-- An op of the model: a request, or an internal op. -/
inductive Op (m : Model) where
  | ext (req : m.External)
  | int (req : m.Internal)

/-- The outcomes of an op in a state at a time. -/
def Op.outs : Op m → m.State → Time → List (Outcome m)
  | .ext r, s, now => (m.external r s now).val.map fun o => ⟨o.next, some o.resp, o.work, o.send⟩
  | .int r, s, now => (m.internal r s now).map fun o => ⟨o.next, none, o.work, o.send⟩

/-! ## The declaration, and its conditions -/

/-- Two outcomes alike on keys `ks`: the same response, work and dispatches,
    and the same views at `ks`. -/
def Alike {K V : Type} (view : m.State → K → V) (ks : List K) (o o' : Outcome m) : Prop :=
  o.resp = o'.resp ∧ o.work = o'.work ∧ o.send = o'.send ∧ ∀ k ∈ ks, view o.next k = view o'.next k

/-- Two outcome lists alike on `ks`, outcome for outcome. -/
def Agree {K V : Type} (view : m.State → K → V) (ks : List K) (outs outs' : List (Outcome m)) : Prop :=
  ∀ i : Nat, match outs[i]?, outs'[i]? with
    | some o, some o' => Alike view ks o o'
    | none, none => True
    | _, _ => False

/-- A footprint for `m`: keys, a view of the state per key, the keys each op
    reads and writes, and the three conditions that make the declaration true. -/
structure Footprint (m : Model) where
  Key  : Type
  View : Type
  /-- What the state holds at a key. -/
  view : m.State → Key → View
  /-- The keys an op reads. -/
  r_set : Op m → List Key
  /-- The keys an op writes. -/
  w_set : Op m → List Key
  /-- The keys cover the state: the views determine it. -/
  complete : ∀ {s s' : m.State}, (∀ k, view s k = view s' k) → s = s'
  /-- An op reads only its read set: in two states that agree on it, the op's
      outcomes agree, outcome for outcome, on the keys it writes. -/
  r_only : ∀ (a : Op m) (s s' : m.State) (now : Time),
    (∀ k ∈ r_set a, view s k = view s' k) → Agree view (w_set a) (a.outs s now) (a.outs s' now)
  /-- An op writes only its write set: every outcome leaves every other view as it was. -/
  w_only : ∀ (a : Op m) (s : m.State) (now : Time) (o : Outcome m),
    o ∈ a.outs s now → ∀ k, k ∉ w_set a → view o.next k = view s k

/-- Bernstein's condition: neither op writes what the other reads or writes. -/
def Footprint.Independent (fp : Footprint m) (a b : Op m) : Prop :=
  (∀ k ∈ fp.w_set a, k ∉ fp.r_set b ∧ k ∉ fp.w_set b) ∧ (∀ k ∈ fp.w_set b, k ∉ fp.r_set a)

/-! ## What the conditions buy: independent ops commute -/

theorem Agree.at {K V : Type} {view : m.State → K → V} {ks : List K}
    {outs outs' : List (Outcome m)} (h : Agree view ks outs outs') {i : Nat} {o : Outcome m}
    (hi : outs[i]? = some o) : ∃ o', outs'[i]? = some o' ∧ Alike view ks o o' := by
  unfold Agree at h
  have := h i
  rw [hi] at this
  split at this
  · rename_i o' h' ho'
    simp only [Option.some.injEq] at h'
    subst h'
    exact ⟨_, ho', this⟩
  · simp_all
  · simp_all

/-- One outcome each, alike: the lists agree. -/
theorem Agree.singleton {K V : Type} {view : m.State → K → V} {ks : List K} {o o' : Outcome m}
    (h : Alike view ks o o') : Agree view ks [o] [o'] := by
  unfold Agree
  intro i
  cases i with
  | zero => exact h
  | succ i => simp

/-- Independent ops commute. From `s`, taking `a`'s `i`-th outcome and then
    `b`'s `j`-th, or `b`'s `j`-th and then `a`'s `i`-th, ends in the same
    state, with the same responses, work and dispatches, pairwise. -/
theorem Footprint.commute (fp : Footprint m) {a b : Op m} (hi : fp.Independent a b)
    {s : m.State} {now : Time} {i j : Nat} {o₁ o₂ : Outcome m}
    (h₁ : (a.outs s now)[i]? = some o₁) (h₂ : (b.outs o₁.next now)[j]? = some o₂) :
    ∃ o₂' o₁' : Outcome m,
      (b.outs s now)[j]? = some o₂' ∧ (a.outs o₂'.next now)[i]? = some o₁' ∧
      o₁'.next = o₂.next ∧
      o₂'.resp = o₂.resp ∧ o₂'.work = o₂.work ∧ o₂'.send = o₂.send ∧
      o₁'.resp = o₁.resp ∧ o₁'.work = o₁.work ∧ o₁'.send = o₁.send := by
  obtain ⟨hab, hba⟩ := hi
  have m₁ : o₁ ∈ a.outs s now := List.mem_of_getElem? h₁
  have m₂ : o₂ ∈ b.outs o₁.next now := List.mem_of_getElem? h₂
  -- `a` wrote nothing `b` reads, so `b` sees the same views as in `s`.
  have agree_b : ∀ k ∈ fp.r_set b, fp.view o₁.next k = fp.view s k :=
    fun k hk => fp.w_only a s now o₁ m₁ k (fun ha => (hab k ha).1 hk)
  obtain ⟨o₂', h₂', like₂⟩ := (fp.r_only b o₁.next s now agree_b).at h₂
  have m₂' : o₂' ∈ b.outs s now := List.mem_of_getElem? h₂'
  -- `b` from `s` wrote nothing `a` reads, so `a` sees the same views as in `s`.
  have agree_a : ∀ k ∈ fp.r_set a, fp.view o₂'.next k = fp.view s k :=
    fun k hk => fp.w_only b s now o₂' m₂' k (fun hb => hba k hb hk)
  obtain ⟨o₁', h₁', like₁⟩ :=
    (fp.r_only a s o₂'.next now (fun k hk => (agree_a k hk).symm)).at h₁
  have m₁' : o₁' ∈ a.outs o₂'.next now := List.mem_of_getElem? h₁'
  refine ⟨o₂', o₁', h₂', h₁', ?_, like₂.1.symm, like₂.2.1.symm, like₂.2.2.1.symm,
    like₁.1.symm, like₁.2.1.symm, like₁.2.2.1.symm⟩
  -- The two final states agree at every key.
  apply fp.complete
  intro k
  by_cases ka : k ∈ fp.w_set a
  · have hb : k ∉ fp.w_set b := (hab k ka).2
    rw [← like₁.2.2.2 k ka, fp.w_only b o₁.next now o₂ m₂ k hb]
  · by_cases kb : k ∈ fp.w_set b
    · rw [fp.w_only a o₂'.next now o₁' m₁' k ka, like₂.2.2.2 k kb]
    · rw [fp.w_only a o₂'.next now o₁' m₁' k ka, fp.w_only b s now o₂' m₂' k kb,
        fp.w_only b o₁.next now o₂ m₂ k kb, fp.w_only a s now o₁ m₁ k ka]

/-! ## An instance: a bank, one key per account -/

/-- Accounts hold balances; `deposit (a, n)` adds `n` to `a` and answers the
    new balance. No internal ops. -/
abbrev bank : Model where
  State    := Nat → Nat
  External := Nat × Nat
  Response := Nat
  Internal := Empty
  Dispatch := Empty
  external := fun (a, n) s _ => .one ⟨fun k => if k = a then s a + n else s k, s a + n, [], []⟩
  internal := fun e _ _ => nomatch e

/-- Each deposit reads and writes its account and nothing else. -/
def bankFootprint : Footprint bank where
  Key  := Nat
  View := Nat
  view := fun s k => s k
  r_set := fun | .ext (a, _) => [a] | .int e => nomatch e
  w_set := fun | .ext (a, _) => [a] | .int e => nomatch e
  complete := fun h => funext h
  r_only := by
    rintro (⟨a, n⟩ | e) s s' now hs
    · have hs := hs a (List.mem_singleton_self a)
      apply Agree.singleton
      refine ⟨by show some (s a + n) = some (s' a + n); rw [hs], rfl, rfl, fun k hk => ?_⟩
      have hk := List.mem_singleton.mp hk
      subst hk
      show (if k = k then s k + n else s k) = (if k = k then s' k + n else s' k)
      simp [hs]
    · exact nomatch e
  w_only := by
    rintro (⟨a, n⟩ | e) s now o ho k hk
    · have ho := List.mem_singleton.mp ho
      subst ho
      have hk : k ≠ a := fun h => hk (h ▸ List.mem_singleton_self k)
      show (if k = a then s a + n else s k) = s k
      simp [hk]
    · exact nomatch e

/-- Deposits to different accounts commute: the generic theorem, applied.
    Whatever order the two deposits settle in, the balances end the same. -/
example {s : Nat → Nat} {x y : Nat} (h : x ≠ y) {o₁ o₂ : Outcome bank}
    (h₁ : ((Op.ext (x, 3)).outs s 0)[0]? = some o₁) (h₂ : ((Op.ext (y, 5)).outs o₁.next 0)[0]? = some o₂) :
    ∃ o₂' o₁' : Outcome bank,
      ((Op.ext (y, 5)).outs s 0)[0]? = some o₂' ∧ ((Op.ext (x, 3)).outs o₂'.next 0)[0]? = some o₁' ∧
      o₁'.next = o₂.next := by
  have hd : bankFootprint.Independent (.ext (x, 3)) (.ext (y, 5)) := by
    refine ⟨fun k hk => ⟨fun hy => ?_, fun hy => ?_⟩, fun k hk hy => ?_⟩ <;>
      first
        | exact h ((List.mem_singleton.mp hk).symm.trans (List.mem_singleton.mp hy))
        | exact h ((List.mem_singleton.mp hk).symm.trans (List.mem_singleton.mp hy)).symm
  obtain ⟨o₂', o₁', h₂', h₁', hnext, -⟩ := bankFootprint.commute hd h₁ h₂
  exact ⟨o₂', o₁', h₂', h₁', hnext⟩

end Accordant

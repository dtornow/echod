import Accordant

/-!
# Footprints: what an op touches, and what that buys

A footprint says which keys of the state an op may read or write. Its
meaning, the thing a checker can use, is that ops on disjoint keys commute:
taking `a` then `b` comes out the same as `b` then `a`, outcome for outcome.
That is what lets a search explore one order instead of both, and what lets
a system shard, lock or partition by key.

This file defines

* `Footprint m`: the declaration, and the obligations a model discharges so
  the declaration is true. They are structural: the state is seen through a
  `view` per key; an op's outcomes depend only on the views at its keys
  (`local_`), and change no other view (`frame`).
* `Footprint.commute`: from those obligations, ops with disjoint footprints
  commute. Proved once, for every model.

A model author declares keys and proves `frame` and `local_`, both about
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

/-! ## The declaration, and its obligations -/

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

/-- The keys of an op, from the two declarations. -/
def opKeys {K : Type} (ext : m.External → List K) (int : m.Internal → List K) : Op m → List K
  | .ext r => ext r
  | .int r => int r

/-- A footprint for `m`: keys, a view of the state per key, which keys each
    op touches, and the two facts that make it true. -/
structure Footprint (m : Model) where
  Key  : Type
  View : Type
  /-- What the state holds at a key. -/
  view : m.State → Key → View
  /-- The views determine the state. -/
  ext  : ∀ {s s' : m.State}, (∀ k, view s k = view s' k) → s = s'
  /-- The keys a request may read or write. -/
  external : m.External → List Key
  /-- The keys an internal op may read or write. -/
  internal : m.Internal → List Key
  /-- An op writes only its keys: every outcome leaves every other view as it was. -/
  frame : ∀ (a : Op m) (s : m.State) (now : Time) (o : Outcome m),
    o ∈ a.outs s now → ∀ k, k ∉ opKeys external internal a → view o.next k = view s k
  /-- An op reads only its keys: in two states that agree on them, its
      outcomes agree on them, outcome for outcome. -/
  local_ : ∀ (a : Op m) (s s' : m.State) (now : Time),
    (∀ k ∈ opKeys external internal a, view s k = view s' k) →
    Agree view (opKeys external internal a) (a.outs s now) (a.outs s' now)

def Footprint.keys (fp : Footprint m) : Op m → List fp.Key :=
  opKeys fp.external fp.internal

def Disjoint {K : Type} (ka kb : List K) : Prop := ∀ k, k ∈ ka → k ∉ kb

/-! ## What the obligations buy: ops on disjoint keys commute -/

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

/-- Ops with disjoint footprints commute. From `s`, taking `a`'s `i`-th outcome
    and then `b`'s `j`-th, or `b`'s `j`-th and then `a`'s `i`-th, ends in the
    same state, with the same responses, work and dispatches, pairwise. -/
theorem Footprint.commute (fp : Footprint m) {a b : Op m} (hd : Disjoint (fp.keys a) (fp.keys b))
    {s : m.State} {now : Time} {i j : Nat} {o₁ o₂ : Outcome m}
    (h₁ : (a.outs s now)[i]? = some o₁) (h₂ : (b.outs o₁.next now)[j]? = some o₂) :
    ∃ o₂' o₁' : Outcome m,
      (b.outs s now)[j]? = some o₂' ∧ (a.outs o₂'.next now)[i]? = some o₁' ∧
      o₁'.next = o₂.next ∧
      o₂'.resp = o₂.resp ∧ o₂'.work = o₂.work ∧ o₂'.send = o₂.send ∧
      o₁'.resp = o₁.resp ∧ o₁'.work = o₁.work ∧ o₁'.send = o₁.send := by
  have m₁ : o₁ ∈ a.outs s now := List.mem_of_getElem? h₁
  have m₂ : o₂ ∈ b.outs o₁.next now := List.mem_of_getElem? h₂
  -- `a` left `b`'s keys alone, so `b` sees the same views as in `s`.
  have agree_b : ∀ k ∈ fp.keys b, fp.view o₁.next k = fp.view s k :=
    fun k hk => fp.frame a s now o₁ m₁ k (fun ha => hd k ha hk)
  obtain ⟨o₂', h₂', like₂⟩ := (fp.local_ b o₁.next s now agree_b).at h₂
  have m₂' : o₂' ∈ b.outs s now := List.mem_of_getElem? h₂'
  -- `b` from `s` left `a`'s keys alone, so `a` sees the same views as in `s`.
  have agree_a : ∀ k ∈ fp.keys a, fp.view o₂'.next k = fp.view s k :=
    fun k hk => fp.frame b s now o₂' m₂' k (fun hb => hd k hk hb)
  obtain ⟨o₁', h₁', like₁⟩ :=
    (fp.local_ a s o₂'.next now (fun k hk => (agree_a k hk).symm)).at h₁
  have m₁' : o₁' ∈ a.outs o₂'.next now := List.mem_of_getElem? h₁'
  refine ⟨o₂', o₁', h₂', h₁', ?_, like₂.1.symm, like₂.2.1.symm, like₂.2.2.1.symm,
    like₁.1.symm, like₁.2.1.symm, like₁.2.2.1.symm⟩
  -- The two final states agree on every key.
  apply fp.ext
  intro k
  by_cases ka : k ∈ fp.keys a
  · have hb : k ∉ fp.keys b := hd k ka
    rw [← like₁.2.2.2 k ka, fp.frame b o₁.next now o₂ m₂ k hb]
  · by_cases kb : k ∈ fp.keys b
    · rw [fp.frame a o₂'.next now o₁' m₁' k ka, like₂.2.2.2 k kb]
    · rw [fp.frame a o₂'.next now o₁' m₁' k ka, fp.frame b s now o₂' m₂' k kb,
        fp.frame b o₁.next now o₂ m₂ k kb, fp.frame a s now o₁ m₁ k ka]

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

/-- Each deposit touches its account and nothing else. -/
def bankFootprint : Footprint bank where
  Key  := Nat
  View := Nat
  view := fun s k => s k
  ext  := fun h => funext h
  external := fun (a, _) => [a]
  internal := fun e => nomatch e
  frame := by
    rintro (⟨a, n⟩ | e) s now o ho k hk
    · have ho := List.mem_singleton.mp ho
      subst ho
      simp [opKeys] at hk
      show (if k = a then s a + n else s k) = s k
      simp [hk]
    · exact nomatch e
  local_ := by
    rintro (⟨a, n⟩ | e) s s' now hs
    · simp [opKeys] at hs
      apply Agree.singleton
      refine ⟨by show some (s a + n) = some (s' a + n); rw [hs], rfl, rfl, fun k hk => ?_⟩
      simp [opKeys] at hk
      subst hk
      show (if k = k then s k + n else s k) = (if k = k then s' k + n else s' k)
      simp [hs]
    · exact nomatch e

/-- Deposits to different accounts commute: the generic theorem, applied.
    Whatever order the two deposits settle in, the balances end the same. -/
example {s : Nat → Nat} {x y : Nat} (h : x ≠ y) {o₁ o₂ : Outcome bank}
    (h₁ : ((Op.ext (x, 3)).outs s 0)[0]? = some o₁) (h₂ : ((Op.ext (y, 5)).outs o₁.next 0)[0]? = some o₂) :
    ∃ o₂' o₁' : Outcome bank,
      ((Op.ext (y, 5)).outs s 0)[0]? = some o₂' ∧ ((Op.ext (x, 3)).outs o₂'.next 0)[0]? = some o₁' ∧
      o₁'.next = o₂.next := by
  have hd : Disjoint (bankFootprint.keys (.ext (x, 3))) (bankFootprint.keys (.ext (y, 5))) := by
    intro k hk hy
    exact h ((List.mem_singleton.mp hk).symm.trans (List.mem_singleton.mp hy))
  obtain ⟨o₂', o₁', h₂', h₁', hnext, -⟩ := bankFootprint.commute hd h₁ h₂
  exact ⟨o₂', o₁', h₂', h₁', hnext⟩

end Accordant

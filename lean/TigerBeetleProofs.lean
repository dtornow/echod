import TigerBeetle

/-!
# TigerBeetle: `debits_must_not_exceed_credits` holds in every reachable state

The theorem, at the bottom:

```
theorem debits_must_not_exceed_credits (lim : Limits) (x : Execution (model lim))
    (hx : Legal (model lim) (initial {}) x) :
    ∀ p ∈ x, ∀ id a, get p.2.state.accounts id = some a → a.debits_must_not_exceed_credits
```

Whatever TigerBeetle does from an empty cluster (requests taking effect, pulses
expiring transfers, in any order the accordant semantics allows), every account
keeps its rule.

The rule alone is not inductive. Posting a pending transfer takes its full amount
out of `debits_pending` and adds at most that to `debits_posted`; that keeps the
rule only if `debits_pending` holds the amount. So the proof carries `Server.Inv`:
the rule, plus that each account's `debits_pending` covers its still-pending debit
transfers (`pending_debits`), plus what that needs about how transfers and their
statuses are stored. Then:

* `Inv.add_account`, `Inv.create`, `Inv.complete`, `Inv.append_settled`: the four
  ways a step changes accounts and transfers keep `Inv`.
* `Inv.create_account`, `Inv.create_transfer`, `Inv.post_or_void`, `Inv.expire`:
  every check that fails leaves the state alone; the one success is one of the
  four changes above.
* `Batch.Inv.run`: a batch keeps `Inv`, because a broken linked chain rolls back
  to the state saved before it, which had `Inv`.
* `Inv.step`, `Inv.legal`: every step of an execution keeps `Inv`; the empty
  cluster has it.
-/

namespace TigerBeetle

/-- `omega`, seeing through `Amount` and `Time` (it does not unfold abbreviations). -/
macro "omega'" : tactic => `(tactic| ((try simp only [Amount, Time] at *) <;> omega))

/-! ## Lookups and replacements -/

theorem get_cons {α : Type} (k id : Id) (v : α) (l : List (Id × α)) :
    get ((k, v) :: l) id = if k = id then some v else get l id := by
  unfold get
  by_cases h : k = id
  · subst h; simp [List.find?]
  · have : (k == id) = false := by simpa using h
    simp [List.find?, this, h]

theorem get_nil {α : Type} (id : Id) : get ([] : List (Id × α)) id = none := rfl

theorem get_append_one {α : Type} (l : List (Id × α)) (k id : Id) (v : α) :
    get (l ++ [(k, v)]) id = (get l id).or (if k = id then some v else none) := by
  induction l with
  | nil => simp [get_nil, get_cons]
  | cons x xs ih =>
    obtain ⟨k', v'⟩ := x
    simp only [List.cons_append, get_cons, ih]
    split <;> simp

theorem get_put {α : Type} (l : List (Id × α)) (k id : Id) (v : α) :
    get (put l k v) id = if k = id then (get l id).map (fun _ => v) else get l id := by
  induction l with
  | nil => simp [put, get_nil]
  | cons x xs ih =>
    obtain ⟨k', v'⟩ := x
    have hput : put ((k', v') :: xs) k v =
        (if k' = k then (k, v) else (k', v')) :: put xs k v := by
      simp [put]
    rw [hput]
    by_cases h : k' = k
    · subst h
      rw [if_pos rfl, get_cons, get_cons, ih]
      by_cases h3 : k' = id <;> simp [h3]
    · rw [if_neg h, get_cons, get_cons, ih]
      by_cases h2 : k' = id <;> by_cases h3 : k = id <;> simp_all

theorem mem_of_get {α : Type} {l : List (Id × α)} {id : Id} {a : α} (h : get l id = some a) :
    (id, a) ∈ l := by
  induction l with
  | nil => simp [get_nil] at h
  | cons x xs ih =>
    obtain ⟨k, v⟩ := x
    rw [get_cons] at h
    split at h
    · simp_all
    · exact List.mem_cons_of_mem _ (ih h)

theorem get_ne_none_of_mem {α : Type} {l : List (Id × α)} {id : Id} {a : α} (h : (id, a) ∈ l) :
    get l id ≠ none := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    obtain ⟨k, v⟩ := x
    rw [get_cons]
    split
    · simp
    · rcases List.mem_cons.mp h with h | h
      · simp_all
      · exact ih h

theorem get_eq_none {α : Type} {l : List (Id × α)} {id : Id} (h : get l id = none) :
    ∀ x ∈ l, x.1 ≠ id := by
  intro x hx heq
  obtain ⟨k, v⟩ := x
  simp only at heq; subst heq
  exact get_ne_none_of_mem hx h

theorem not_mem_keys {α : Type} {l : List (Id × α)} {id : Id} (h : get l id = none) :
    id ∉ l.map (·.1) := by
  intro hm
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
  exact get_eq_none h x hx rfl

/-! ## Sums over filters -/

section Sums
variable {α : Type} (w : α → Nat)

theorem sum_filter_mono (l : List α) (f g : α → Bool) (h : ∀ x ∈ l, g x = true → f x = true) :
    ((l.filter g).map w).sum ≤ ((l.filter f).map w).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have ih := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x (List.mem_cons_self ..)
    by_cases hg : g x <;> by_cases hf : f x <;> simp_all <;> omega

theorem sum_filter_drop (l : List α) (f g : α → Bool) (y : α) (hy : y ∈ l) (hfy : f y = true)
    (hgy : g y = false) (h : ∀ x ∈ l, g x = true → f x = true) :
    ((l.filter g).map w).sum + w y ≤ ((l.filter f).map w).sum := by
  induction l with
  | nil => simp at hy
  | cons x xs ih =>
    have hmono := sum_filter_mono w xs f g (fun z hz => h z (List.mem_cons_of_mem _ hz))
    rcases List.mem_cons.mp hy with rfl | hy
    · simp [hfy, hgy]; omega
    · have ih := ih hy (fun z hz => h z (List.mem_cons_of_mem _ hz))
      have hx := h x (List.mem_cons_self ..)
      by_cases hg : g x <;> by_cases hf : f x <;> simp_all <;> omega

theorem sum_filter_zero (l : List α) (f : α → Bool) (h : ∀ x ∈ l, f x = false) :
    ((l.filter f).map w).sum = 0 := by
  rw [List.filter_eq_nil_iff.mpr (fun x hx => by simp [h x hx])]; rfl

theorem le_sum_filter (l : List α) (f : α → Bool) (y : α) (hy : y ∈ l) (hfy : f y = true) :
    w y ≤ ((l.filter f).map w).sum := by
  have := sum_filter_drop w l f (fun _ => false) y hy hfy rfl (by simp)
  have h0 : ((l.filter fun _ => false).map w).sum = 0 :=
    sum_filter_zero w l _ (fun _ _ => rfl)
  omega

end Sums

/-! ## More about lookups -/

theorem get_append_one_of_some {α : Type} {l : List (Id × α)} {k id : Id} {v a : α}
    (h : get l id = some a) : get (l ++ [(k, v)]) id = some a := by
  rw [get_append_one, h]; rfl

theorem get_append_one_ne_none {α : Type} {l : List (Id × α)} {k id : Id} {v : α}
    (h : get l id ≠ none) : get (l ++ [(k, v)]) id ≠ none := by
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp h
  rw [get_append_one_of_some ha]; simp

theorem get_append_one_of_ne {α : Type} {l : List (Id × α)} {k id : Id} {v : α}
    (h : k ≠ id) : get (l ++ [(k, v)]) id = get l id := by
  rw [get_append_one]; simp [h]

theorem get_append_one_self {α : Type} {l : List (Id × α)} {k : Id} {v : α}
    (h : get l k = none) : get (l ++ [(k, v)]) k = some v := by
  rw [get_append_one, h]; simp

theorem ne_none_of_get_append_one {α : Type} {l : List (Id × α)} {k id : Id} {v : α}
    (h : get (l ++ [(k, v)]) id ≠ none) : get l id ≠ none ∨ k = id := by
  rw [get_append_one] at h
  cases hg : get l id <;> simp_all

theorem get_put_ne_none {α : Type} {l : List (Id × α)} {k id : Id} {v : α} :
    get (put l k v) id ≠ none ↔ get l id ≠ none := by
  rw [get_put]; split <;> simp

theorem get_put_of_ne {α : Type} {l : List (Id × α)} {k id : Id} {v : α} (h : k ≠ id) :
    get (put l k v) id = get l id := by
  rw [get_put, if_neg h]

theorem get_put_self {α : Type} {l : List (Id × α)} {k : Id} {v a : α} (h : get l k = some a) :
    get (put l k v) k = some v := by
  rw [get_put, if_pos rfl, h]; rfl

/-- After two replacements, an account is one of the two new ones or an old one. -/
theorem get_put2 {α : Type} {l : List (Id × α)} {d c id : Id} {x y a : α}
    (hd : get l d ≠ none) (hc : get l c ≠ none) (hne : d ≠ c)
    (h : get (put (put l d x) c y) id = some a) :
    (id = c ∧ a = y) ∨ (id = d ∧ a = x) ∨ (id ≠ c ∧ id ≠ d ∧ get l id = some a) := by
  rw [get_put, get_put] at h
  by_cases h1 : c = id
  · subst h1; left
    rw [if_pos rfl, if_neg hne] at h
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hc
    rw [hb] at h; simp at h; exact ⟨rfl, h.symm⟩
  · rw [if_neg h1] at h
    by_cases h2 : d = id
    · subst h2; right; left
      rw [if_pos rfl] at h
      obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hd
      rw [hb] at h; simp at h; exact ⟨rfl, h.symm⟩
    · rw [if_neg h2] at h
      exact Or.inr (Or.inr ⟨Ne.symm h1, Ne.symm h2, h⟩)

/-! ## The invariant

The rule alone is not preserved: posting a pending transfer takes its amount out
of `debits_pending`, which is safe only if `debits_pending` covers it. So the
invariant also says that an account's `debits_pending` covers its pending debits,
and what that needs about how transfers and their statuses are stored. -/

/-- Whether a transfer is a still-pending debit of account `a`. -/
def counted (P : List (Id × TransferPendingStatus)) (a : Id) (x : Id × Transfer) : Bool :=
  x.2.debit_account_id == a && get P x.1 == some .pending

/-- What account `a`'s `debits_pending` must cover: the amounts of its pending
    debit transfers that are still pending. -/
def Server.pending_debits (s : Server) (a : Id) : Nat :=
  ((s.transfers.filter (counted s.transfers_pending a)).map (·.2.amount)).sum

structure Server.Inv (s : Server) : Prop where
  /-- Every account keeps the rule. -/
  rule : ∀ id a, get s.accounts id = some a → a.debits_must_not_exceed_credits
  /-- Every account's `debits_pending` covers its pending debits. -/
  covered : ∀ id a, get s.accounts id = some a → s.pending_debits id ≤ a.debits_pending
  /-- Every pending transfer has a status. -/
  status : ∀ x ∈ s.transfers, x.2.flags.pending = true → get s.transfers_pending x.1 ≠ none
  /-- A status is never `none`: only pending transfers have one. -/
  not_none : ∀ id, get s.transfers_pending id ≠ some .none
  /-- Every status is a stored transfer's. -/
  stored : ∀ id, get s.transfers_pending id ≠ none → get s.transfers id ≠ none
  /-- Every transfer's debit account exists. -/
  debit_exists : ∀ x ∈ s.transfers, get s.accounts x.2.debit_account_id ≠ none
  /-- No transfer debits and credits the same account. -/
  distinct : ∀ x ∈ s.transfers, x.2.debit_account_id ≠ x.2.credit_account_id
  /-- Transfer ids are unique. -/
  unique : (s.transfers.map (·.1)).Nodup

theorem Server.Inv.status_none {s : Server} (h : s.Inv) {id : Id} (hT : get s.transfers id = none) :
    get s.transfers_pending id = none := by
  cases hg : get s.transfers_pending id with
  | none => rfl
  | some v => exact absurd hT (h.stored id (by simp [hg]))

/-- The invariant reads only accounts, transfers and statuses. -/
theorem Server.Inv.congr {s s' : Server} (h : s.Inv) (ha : s'.accounts = s.accounts)
    (ht : s'.transfers = s.transfers) (hp : s'.transfers_pending = s.transfers_pending) :
    s'.Inv := by
  have hd : ∀ id, s'.pending_debits id = s.pending_debits id := by
    intro id; simp [Server.pending_debits, ht, hp]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ha]; exact h.rule
  · rw [ha]; intro id a hg; rw [hd]; exact h.covered id a hg
  · rw [ht, hp]; exact h.status
  · rw [hp]; exact h.not_none
  · rw [ht, hp]; exact h.stored
  · rw [ht, ha]; exact h.debit_exists
  · rw [ht]; exact h.distinct
  · rw [ht]; exact h.unique

theorem Server.Inv.empty : ({} : Server).Inv :=
  ⟨by simp [get_nil], by simp [get_nil], by simp, by simp [get_nil], by simp [get_nil], by simp,
   by simp, by simp⟩

/-! ## The ways a step changes the state -/

/-- A new account starts with nothing. -/
theorem Server.Inv.add_account {s s' : Server} {id : Id} {acc : Account} (h : s.Inv)
    (hn : get s.accounts id = none) (h0 : acc.debits_pending = 0) (h1 : acc.debits_posted = 0)
    (ha : s'.accounts = s.accounts ++ [(id, acc)]) (ht : s'.transfers = s.transfers)
    (hp : s'.transfers_pending = s.transfers_pending) : s'.Inv := by
  have hd : ∀ a, s'.pending_debits a = s.pending_debits a := by
    intro a; simp [Server.pending_debits, ht, hp]
  -- An account that does not exist has no pending debits.
  have hz : s.pending_debits id = 0 := by
    apply sum_filter_zero
    intro x hx
    have := h.debit_exists x hx
    have hne : x.2.debit_account_id ≠ id := fun heq => by rw [heq] at this; exact this hn
    simp [counted, hne]
  have hcases : ∀ id' a, get s'.accounts id' = some a →
      get s.accounts id' = some a ∨ (id' = id ∧ a = acc) := by
    intro id' a hg
    rw [ha, get_append_one] at hg
    cases hg' : get s.accounts id' with
    | some b => rw [hg'] at hg; simp at hg; exact Or.inl (hg ▸ rfl)
    | none =>
      rw [hg'] at hg
      by_cases he : id = id' <;> simp [he] at hg
      exact Or.inr ⟨he.symm, hg.symm⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro id' a hg
    rcases hcases id' a hg with hg | ⟨rfl, rfl⟩
    · exact h.rule id' a hg
    · unfold Account.debits_must_not_exceed_credits; rw [h0, h1]; intro _; exact Nat.zero_le _
  · intro id' a hg
    rw [hd]
    rcases hcases id' a hg with hg | ⟨rfl, rfl⟩
    · exact h.covered id' a hg
    · omega'
  · rw [ht, hp]; exact h.status
  · rw [hp]; exact h.not_none
  · rw [ht, hp]; exact h.stored
  · rw [ht, ha]; intro x hx; exact get_append_one_ne_none (h.debit_exists x hx)
  · rw [ht]; exact h.distinct
  · rw [ht]; exact h.unique

/-- Creates a single-phase or pending transfer, `tid`, debiting `d` and crediting `c`. -/
theorem Server.Inv.create {s s' : Server} {tid d c : Id} {tr : Transfer} {dr cr dr' cr' : Account}
    (h : s.Inv)
    (ht : s'.transfers = s.transfers ++ [(tid, tr)])
    (hp : s'.transfers_pending = if tr.flags.pending
      then s.transfers_pending ++ [(tid, .pending)] else s.transfers_pending)
    (ha : s'.accounts = put (put s.accounts d dr') c cr')
    (hT : get s.transfers tid = none)
    (hd : get s.accounts d = some dr) (hc : get s.accounts c = some cr) (hne : d ≠ c)
    (htd : tr.debit_account_id = d) (htc : tr.credit_account_id = c)
    (hdr_rule : dr'.debits_must_not_exceed_credits)
    (hdr_dp : dr'.debits_pending = dr.debits_pending + (if tr.flags.pending then tr.amount else 0))
    (hcr_dp : cr'.debits_pending = cr.debits_pending)
    (hcr_dpo : cr'.debits_posted = cr.debits_posted)
    (hcr_cp : cr.credits_posted ≤ cr'.credits_posted)
    (hcr_flag : cr'.flags.debits_must_not_exceed_credits = cr.flags.debits_must_not_exceed_credits) :
    s'.Inv := by
  have hP := h.status_none hT
  -- Old transfers keep their statuses; the new one is counted if pending.
  have hold : ∀ x ∈ s.transfers, get s'.transfers_pending x.1 = get s.transfers_pending x.1 := by
    intro x hx
    have hne : tid ≠ x.1 := fun heq => get_eq_none hT x hx heq.symm
    rw [hp]; split
    · exact get_append_one_of_ne hne
    · rfl
  have hnew : get s'.transfers_pending tid = if tr.flags.pending then some .pending else none := by
    rw [hp]; split
    · exact get_append_one_self hP
    · exact hP
  have hpd : ∀ a, s'.pending_debits a =
      s.pending_debits a + (if tr.flags.pending && d == a then tr.amount else 0) := by
    intro a
    unfold Server.pending_debits
    rw [ht, List.filter_append, List.map_append, List.sum_append]
    congr 1
    · congr 2
      apply List.filter_congr
      intro x hx
      simp [counted, hold x hx]
    · simp only [List.filter_cons, List.filter_nil, counted, hnew, htd]
      cases tr.flags.pending <;> by_cases hda : d = a <;> simp [hda]
  have hdn : get s.accounts d ≠ none := by simp [hd]
  have hcn : get s.accounts c ≠ none := by simp [hc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro id a hg
    rw [ha] at hg
    rcases get_put2 hdn hcn hne hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨_, _, hg⟩
    · have := h.rule id cr hc
      unfold Account.debits_must_not_exceed_credits at this ⊢
      intro hf; rw [hcr_flag] at hf; have := this hf; omega'
    · exact hdr_rule
    · exact h.rule id a hg
  · intro id a hg
    rw [ha] at hg
    rw [hpd]
    rcases get_put2 hdn hcn hne hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨_, hid, hg⟩
    · have := h.covered id cr hc
      have : (d == id) = false := by simpa using hne
      simp [this]; omega'
    · have := h.covered id dr hd
      rw [hdr_dp]; cases tr.flags.pending <;> simp <;> omega'
    · have := h.covered id a hg
      have : (d == id) = false := by simpa using Ne.symm hid
      simp [this]; omega'
  · intro x hx hpend
    rw [ht] at hx
    rcases List.mem_append.mp hx with hx | hx
    · rw [hold x hx]; exact h.status x hx hpend
    · simp at hx; subst hx; simp only at hpend ⊢; rw [hnew, hpend]; simp
  · intro id
    rw [hp]; split
    · rw [get_append_one]
      cases hg : get s.transfers_pending id with
      | some v => have := h.not_none id; rw [hg] at this; simpa using this
      | none => by_cases hid : tid = id <;> simp [hid]
    · exact h.not_none id
  · intro id hg
    rw [ht]
    by_cases hid : tid = id
    · subst hid; rw [get_append_one_self hT]; simp
    · rw [get_append_one_of_ne hid]
      rw [hp] at hg
      split at hg
      · rcases ne_none_of_get_append_one hg with hg | hg
        · exact h.stored id hg
        · exact absurd hg hid
      · exact h.stored id hg
  · intro x hx
    rw [ha, get_put_ne_none, get_put_ne_none]
    rw [ht] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact h.debit_exists x hx
    · simp at hx; subst hx; simp only; rw [htd]; exact hdn
  · intro x hx
    rw [ht] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact h.distinct x hx
    · simp at hx; subst hx; simp only; rw [htd, htc]; exact hne
  · rw [ht, List.map_append, List.nodup_append]
    refine ⟨h.unique, by simp, ?_⟩
    intro a ha b hb heq
    simp at hb; subst hb; subst heq
    exact not_mem_keys hT ha

/-- Completes the pending transfer `pid` (post, void or expiry): its status moves on
    from `pending`, and its amount leaves the debit account's `debits_pending`. -/
theorem Server.Inv.complete {s s' : Server} {pid d c : Id} {p : Transfer}
    {st : TransferPendingStatus} {dr cr dr' cr' : Account}
    (h : s.Inv)
    (ht : s'.transfers = s.transfers)
    (hP : s'.transfers_pending = put s.transfers_pending pid st)
    (ha : s'.accounts = put (put s.accounts d dr') c cr')
    (hp : (pid, p) ∈ s.transfers)
    (hstat : get s.transfers_pending pid = some .pending) (hst : st ≠ .pending)
    (hst' : st ≠ .none)
    (hpd : p.debit_account_id = d) (hpc : p.credit_account_id = c)
    (hd : get s.accounts d = some dr) (hc : get s.accounts c = some cr)
    (hdr_dp : dr'.debits_pending = dr.debits_pending - p.amount)
    (hdr_dpo : dr'.debits_posted ≤ dr.debits_posted + p.amount)
    (hdr_cp : dr.credits_posted ≤ dr'.credits_posted)
    (hdr_flag : dr'.flags.debits_must_not_exceed_credits = dr.flags.debits_must_not_exceed_credits)
    (hcr_dp : cr'.debits_pending = cr.debits_pending)
    (hcr_dpo : cr'.debits_posted = cr.debits_posted)
    (hcr_cp : cr.credits_posted ≤ cr'.credits_posted)
    (hcr_flag : cr'.flags.debits_must_not_exceed_credits = cr.flags.debits_must_not_exceed_credits) :
    s'.Inv := by
  have hne : d ≠ c := by rw [← hpd, ← hpc]; exact h.distinct _ hp
  -- No transfer becomes counted; `pid` stops being counted.
  have hsub : ∀ a, ∀ x ∈ s.transfers, counted s'.transfers_pending a x = true →
      counted s.transfers_pending a x = true := by
    intro a x _ hx
    simp only [counted, hP, get_put, Bool.and_eq_true, beq_iff_eq] at hx ⊢
    refine ⟨hx.1, ?_⟩
    have := hx.2
    split at this
    · rename_i heq; rw [← heq, hstat] at this; simp at this; exact absurd this hst
    · exact this
  have hpid : ∀ a, counted s'.transfers_pending a (pid, p) = false := by
    intro a
    simp [counted, hP, get_put, hstat, hst]
  have hmono : ∀ a, s'.pending_debits a ≤ s.pending_debits a := by
    intro a; unfold Server.pending_debits; rw [ht]
    exact sum_filter_mono _ _ _ _ (hsub a)
  have hdrop : s'.pending_debits d + p.amount ≤ s.pending_debits d := by
    unfold Server.pending_debits; rw [ht]
    exact sum_filter_drop (·.2.amount) _ _ _ (pid, p) hp (by simp [counted, hpd, hstat])
      (hpid d) (hsub d)
  have hcov_d := h.covered d dr hd
  have hdn : get s.accounts d ≠ none := by simp [hd]
  have hcn : get s.accounts c ≠ none := by simp [hc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro id a hg
    rw [ha] at hg
    rcases get_put2 hdn hcn hne hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨_, _, hg⟩
    · have := h.rule id cr hc
      unfold Account.debits_must_not_exceed_credits at this ⊢
      intro hf; rw [hcr_flag] at hf; have := this hf; omega'
    · have := h.rule id dr hd
      unfold Account.debits_must_not_exceed_credits at this ⊢
      intro hf; rw [hdr_flag] at hf; have := this hf; omega'
    · exact h.rule id a hg
  · intro id a hg
    rw [ha] at hg
    rcases get_put2 hdn hcn hne hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨_, _, hg⟩
    · have := h.covered id cr hc; have := hmono id; omega'
    · omega'
    · have := h.covered id a hg; have := hmono id; omega'
  · intro x hx hpend
    rw [ht] at hx
    rw [hP, get_put_ne_none]; exact h.status x hx hpend
  · intro id
    rw [hP, get_put]; split
    · cases get s.transfers_pending id <;> simp [hst']
    · exact h.not_none id
  · intro id hg
    rw [hP, get_put_ne_none] at hg; rw [ht]; exact h.stored id hg
  · intro x hx
    rw [ha, get_put_ne_none, get_put_ne_none]; rw [ht] at hx; exact h.debit_exists x hx
  · rw [ht]; exact h.distinct
  · rw [ht]; exact h.unique

/-- Appends a transfer that is not pending (a post or a void): it is never counted. -/
theorem Server.Inv.append_settled {s s' : Server} {tid : Id} {tr : Transfer} (h : s.Inv)
    (hT : get s.transfers tid = none) (hpend : tr.flags.pending = false)
    (hdx : get s.accounts tr.debit_account_id ≠ none)
    (hdc : tr.debit_account_id ≠ tr.credit_account_id)
    (ht : s'.transfers = s.transfers ++ [(tid, tr)])
    (hp : s'.transfers_pending = s.transfers_pending) (ha : s'.accounts = s.accounts) :
    s'.Inv := by
  have hP := h.status_none hT
  have hpd : ∀ a, s'.pending_debits a = s.pending_debits a := by
    intro a
    unfold Server.pending_debits
    rw [ht, hp, List.filter_append, List.map_append, List.sum_append]
    simp [counted, hP]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ha]; exact h.rule
  · rw [ha]; intro id a hg; rw [hpd]; exact h.covered id a hg
  · intro x hx hx'
    rw [ht] at hx
    rcases List.mem_append.mp hx with hx | hx
    · rw [hp]; exact h.status x hx hx'
    · simp at hx; subst hx; simp_all
  · rw [hp]; exact h.not_none
  · intro id hg
    rw [hp] at hg; rw [ht]; exact get_append_one_ne_none (h.stored id hg)
  · intro x hx
    rw [ht] at hx; rw [ha]
    rcases List.mem_append.mp hx with hx | hx
    · exact h.debit_exists x hx
    · simp at hx; subst hx; exact hdx
  · intro x hx
    rw [ht] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact h.distinct x hx
    · simp at hx; subst hx; exact hdc
  · rw [ht, List.map_append, List.nodup_append]
    refine ⟨h.unique, by simp, ?_⟩
    intro a ha b hb heq
    simp at hb; subst hb; subst heq
    exact not_mem_keys hT ha

/-! ## The steps -/

theorem Server.Inv.create_account {s : Server} (h : s.Inv) (ts : Time) (a : NewAccount) :
    (s.create_account ts a).1.Inv := by
  unfold Server.create_account
  dsimp only
  split; · exact h
  split; · exact h
  split
  · exact h
  · rename_i hn
    split; · exact h
    split; · exact h
    split; · exact h
    exact h.add_account hn rfl rfl rfl rfl rfl

theorem Server.Inv.insert_transfer {s : Server} (h : s.Inv) {ts : Time} {t : NewTransfer}
    {dr cr : Account} {amount : Amount} (hT : get s.transfers t.id = none)
    (hd : get s.accounts t.debit_account_id = some dr)
    (hc : get s.accounts t.credit_account_id = some cr)
    (hne : t.credit_account_id ≠ t.debit_account_id)
    (hex : dr.debits_exceed_credits amount = false) :
    (s.insert_transfer ts t dr cr amount).1.Inv := by
  unfold Server.insert_transfer
  dsimp only
  refine h.create rfl rfl rfl hT hd hc (Ne.symm hne) rfl rfl ?_ ?_ rfl rfl ?_ ?_
  · unfold Account.debits_must_not_exceed_credits
    simp only [Account.debits_exceed_credits, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hex
    intro hf
    have hf' : dr.flags.debits_must_not_exceed_credits = true := by
      revert hf; split <;> simp
    rcases hex with hex | hex
    · rw [hf'] at hex; contradiction
    · try dsimp only
      split <;> omega'
  · try dsimp only
    split <;> simp_all
  · try dsimp only
    split <;> omega'
  · try dsimp only
    split <;> rfl

theorem Server.Inv.insert_post_or_void {s : Server} (h : s.Inv) {ts : Time} {t : NewTransfer}
    {p : Transfer} {dr cr : Account} {amount : Amount} (hT : get s.transfers t.id = none)
    (hpid : get s.transfers t.pending_id = some p)
    (hstat : get s.transfers_pending t.pending_id = some .pending)
    (hd : get s.accounts p.debit_account_id = some dr)
    (hc : get s.accounts p.credit_account_id = some cr)
    (hamt : amount ≤ p.amount) (hpend : t.flags.pending = false) :
    (s.insert_post_or_void ts t p dr cr amount).1.Inv := by
  unfold Server.insert_post_or_void
  dsimp only
  have hp := mem_of_get hpid
  have h1 := h.complete (s' := { s with
      transfers_pending := put s.transfers_pending t.pending_id
        (if t.flags.post_pending_transfer then .posted else .voided),
      accounts := put (put s.accounts p.debit_account_id
        { dr with
          debits_pending := dr.debits_pending - p.amount,
          debits_posted := if t.flags.post_pending_transfer then dr.debits_posted + amount
            else dr.debits_posted,
          flags := if t.flags.void_pending_transfer && p.flags.closing_debit
            then { dr.flags with closed := false } else dr.flags })
        p.credit_account_id
        { cr with
          credits_pending := cr.credits_pending - p.amount,
          credits_posted := if t.flags.post_pending_transfer then cr.credits_posted + amount
            else cr.credits_posted,
          flags := if t.flags.void_pending_transfer && p.flags.closing_credit
            then { cr.flags with closed := false } else cr.flags } })
    rfl rfl rfl hp hstat (by split <;> simp) (by split <;> simp) rfl rfl hd hc rfl
    (by (try dsimp only); split <;> omega') (Nat.le_refl _) (by (try dsimp only); split <;> rfl)
    rfl rfl (by (try dsimp only); split <;> omega') (by (try dsimp only); split <;> rfl)
  refine h1.append_settled (by exact hT) (by exact hpend) ?_ ?_ rfl rfl rfl
  · simp only; rw [get_put_ne_none, get_put_ne_none]; simp [hd]
  · exact h.distinct _ hp

/-- Peels one check off a step: the state it leads to has `P` if both branches' do.
    (`split` gives up on a chain of thirty checks.) -/
theorem fst_ite {β : Type} {P : Server → Prop} {c : Prop} {inst : Decidable c}
    {a b : Server × β} (ha : c → P a.1) (hb : ¬ c → P b.1) : P (@ite _ c inst a b).1 := by
  cases inst with
  | isTrue hc => exact ha hc
  | isFalse hc => exact hb hc

theorem Server.Inv.post_or_void {s : Server} (h : s.Inv) (ts : Time) (t : NewTransfer)
    (hT : get s.transfers t.id = none) : (s.post_or_void_pending_transfer ts t).1.Inv := by
  unfold Server.post_or_void_pending_transfer
  refine fst_ite (P := Server.Inv) (fun _ => h) (fun _ => ?_)
  refine fst_ite (P := Server.Inv) (fun _ => h) (fun hflags => ?_)
  refine fst_ite (P := Server.Inv) (fun _ => h) (fun _ => ?_)
  refine fst_ite (P := Server.Inv) (fun _ => h) (fun _ => ?_)
  refine fst_ite (P := Server.Inv) (fun _ => h) (fun _ => ?_)
  refine fst_ite (P := Server.Inv) (fun _ => h) (fun _ => ?_)
  rcases hpid : get s.transfers t.pending_id with _ | p
  · exact h
  refine fst_ite (P := Server.Inv) (fun _ => h) (fun hpp => ?_)
  rcases hd : get s.accounts p.debit_account_id with _ | dr
  · exact h
  rcases hc : get s.accounts p.credit_account_id with _ | cr
  · exact h
  refine fst_ite (P := Server.Inv) (fun _ => h) (fun _ => ?_)
  refine fst_ite (P := Server.Inv) (fun _ => h) (fun _ => ?_)
  refine fst_ite (P := Server.Inv) (fun _ => h) (fun _ => ?_)
  refine fst_ite (P := Server.Inv) (fun _ => h) (fun _ => ?_)
  refine fst_ite (P := Server.Inv) (fun _ => h) (fun hamt => ?_)
  refine fst_ite (P := Server.Inv) (fun _ => h) (fun _ => ?_)
  refine fst_ite (P := Server.Inv) (fun _ => h) (fun hposted => ?_)
  refine fst_ite (P := Server.Inv) (fun _ => h) (fun hvoided => ?_)
  refine fst_ite (P := Server.Inv) (fun _ => h) (fun hexpired => ?_)
  refine fst_ite (P := Server.Inv) (fun _ => h) (fun _ => ?_)
  refine fst_ite (P := Server.Inv) (fun _ => h) (fun _ => ?_)
  refine fst_ite (P := Server.Inv) (fun _ => h) (fun _ => ?_)
  have hpp' : p.flags.pending = true := by simpa using hpp
  have hstat : get s.transfers_pending t.pending_id = some .pending := by
    have hne := h.status _ (mem_of_get hpid) hpp'
    rcases hg : get s.transfers_pending t.pending_id with _ | st
    · exact absurd hg hne
    · rw [hg] at hposted hvoided hexpired
      have := h.not_none t.pending_id
      rw [hg] at this
      cases st <;> simp at hposted hvoided hexpired this ⊢
  have hpend : t.flags.pending = false := by
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hflags; exact hflags.1.1.1.1
  exact h.insert_post_or_void hT hpid hstat hd hc (Nat.le_of_not_lt hamt) hpend

theorem Server.Inv.create_transfer {s : Server} (h : s.Inv) (ts : Time) (t : NewTransfer) :
    (s.create_transfer ts t).1.Inv := by
  unfold Server.create_transfer
  refine fst_ite (P := Server.Inv) (fun _ => h) (fun _ => ?_)
  refine fst_ite (P := Server.Inv) (fun _ => h) (fun _ => ?_)
  rcases hT : get s.transfers t.id with _ | e
  · refine fst_ite (P := Server.Inv) (fun _ => h) (fun _ => ?_)
    refine fst_ite (P := Server.Inv) (fun _ => h.post_or_void ts t hT) (fun _ => ?_)
    refine fst_ite (P := Server.Inv) (fun _ => h) (fun _ => ?_)
    refine fst_ite (P := Server.Inv) (fun _ => h) (fun _ => ?_)
    refine fst_ite (P := Server.Inv) (fun _ => h) (fun _ => ?_)
    refine fst_ite (P := Server.Inv) (fun _ => h) (fun _ => ?_)
    refine fst_ite (P := Server.Inv) (fun _ => h) (fun hne => ?_)
    refine fst_ite (P := Server.Inv) (fun _ => h) (fun _ => ?_)
    refine fst_ite (P := Server.Inv) (fun _ => h) (fun _ => ?_)
    refine fst_ite (P := Server.Inv) (fun _ => h) (fun _ => ?_)
    refine fst_ite (P := Server.Inv) (fun _ => h) (fun _ => ?_)
    refine fst_ite (P := Server.Inv) (fun _ => h) (fun _ => ?_)
    rcases hd : get s.accounts t.debit_account_id with _ | dr
    · exact h
    rcases hc : get s.accounts t.credit_account_id with _ | cr
    · exact h
    refine fst_ite (P := Server.Inv) (fun _ => h) (fun _ => ?_)
    refine fst_ite (P := Server.Inv) (fun _ => h) (fun _ => ?_)
    refine fst_ite (P := Server.Inv) (fun _ => h) (fun _ => ?_)
    refine fst_ite (P := Server.Inv) (fun _ => h) (fun _ => ?_)
    refine fst_ite (P := Server.Inv) (fun _ => h) (fun _ => ?_)
    refine fst_ite (P := Server.Inv) (fun _ => h) (fun _ => ?_)
    refine fst_ite (P := Server.Inv) (fun _ => h) (fun _ => ?_)
    refine fst_ite (P := Server.Inv) (fun _ => h) (fun _ => ?_)
    refine fst_ite (P := Server.Inv) (fun _ => h) (fun _ => ?_)
    refine fst_ite (P := Server.Inv) (fun _ => h) (fun _ => ?_)
    refine fst_ite (P := Server.Inv) (fun _ => h) (fun _ => ?_)
    refine fst_ite (P := Server.Inv) (fun _ => h) (fun hex => ?_)
    refine fst_ite (P := Server.Inv) (fun _ => h) (fun _ => ?_)
    exact h.insert_transfer hT hd hc hne (by simpa using hex)
  · exact h

/-! ## Batches: a rolled-back chain goes back to a state that had the invariant -/

/-- The batch's state has the invariant, and so does the state saved before its chain. -/
def Batch.Inv {S : Type} (b : Batch S) : Prop :=
  b.server.Inv ∧ ∀ c, b.chain = some c → c.saved.Inv

theorem Batch.Inv.step {E S : Type} [DecidableEq S]
    {step : Server → Time → E → Server × CreateResult S} {linked : E → Bool}
    {created failed chain_open : S} {on_fail : Server → E → S → Server} {base n i : Nat}
    {b : Batch S} {e : E}
    (hstep : ∀ s ts e, s.Inv → (step s ts e).1.Inv)
    (hfail : ∀ s e st, s.Inv → (on_fail s e st).Inv) (hb : b.Inv) :
    (batch_step step linked created failed chain_open on_fail base n i b e).Inv := by
  obtain ⟨hs, hc⟩ := hb
  unfold batch_step Batch.Inv
  dsimp only
  generalize hch : (if linked e && b.chain.isNone then some (⟨i, b.server, false⟩ : Chain)
    else b.chain) = chain0
  have hchain : ∀ c, chain0 = some c → c.saved.Inv := by
    intro c h; rw [← hch] at h; split at h
    · cases h; exact hs
    · exact hc c h
  generalize hsr : (if linked e && i + 1 = n then (b.server, ⟨base + i + 1, chain_open⟩)
    else if chain0.any (·.broken) then (b.server, ⟨base + i + 1, failed⟩)
    else step b.server (base + i + 1) e : Server × CreateResult S) = sr
  have hsr' : sr.1.Inv := by
    rw [← hsr]; split
    · exact hs
    · split
      · exact hs
      · exact hstep _ _ _ hs
  split
  · refine ⟨hsr', fun c h => ?_⟩
    split at h
    · cases h
    · exact hchain c h
  · rcases hcs : chain0 with _ | c
    · exact ⟨hfail _ _ _ hsr', fun c h => by cases h⟩
    · dsimp only
      split
      · refine ⟨hfail _ _ _ hsr', fun c' h => ?_⟩
        split at h
        · cases h
        · have h' : some c = some c' := h
          cases h'; exact hchain c hcs
      · refine ⟨hfail _ _ _ (hchain c hcs), fun c' h => ?_⟩
        split at h
        · cases h
        · cases h; exact hchain c hcs

theorem Batch.Inv.run {E S : Type} [DecidableEq S]
    {step : Server → Time → E → Server × CreateResult S} {linked : E → Bool}
    {created failed chain_open : S} {on_fail : Server → E → S → Server} {base n : Nat}
    (hstep : ∀ s ts e, s.Inv → (step s ts e).1.Inv)
    (hfail : ∀ s e st, s.Inv → (on_fail s e st).Inv) :
    ∀ (events : List E) (i : Nat) (b : Batch S), b.Inv →
      (run_batch step linked created failed chain_open on_fail base n i events b).Inv
  | [], _, _, hb => hb
  | e :: rest, i, b, hb => by
    unfold run_batch
    exact Batch.Inv.run hstep hfail rest (i + 1) _ (hb.step hstep hfail)

theorem Server.Inv.create_accounts {s : Server} (h : s.Inv) (events : List NewAccount) :
    (s.create_accounts events).1.Inv := by
  unfold Server.create_accounts
  dsimp only
  have := Batch.Inv.run (linked := (·.flags.linked)) (created := CreateAccountStatus.created)
    (failed := .linked_event_failed) (chain_open := .linked_event_chain_open)
    (base := max s.prepare_timestamp s.now) (n := events.length)
    (fun s ts a h => h.create_account ts a) (fun _ _ _ h => h) events 0 ⟨s, none, #[]⟩
    ⟨h, by intro c hc; cases hc⟩
  exact this.1.congr rfl rfl rfl

theorem Server.Inv.spent {s : Server} (h : s.Inv) {t : NewTransfer} {st : CreateTransferStatus} :
    (TigerBeetle.spend s t st).Inv := by
  unfold TigerBeetle.spend; split
  · exact h.congr rfl rfl rfl
  · exact h

theorem Server.Inv.create_transfers {s : Server} (h : s.Inv) (events : List NewTransfer) :
    (s.create_transfers events).1.Inv := by
  unfold Server.create_transfers
  dsimp only
  have := Batch.Inv.run (linked := (·.flags.linked)) (created := CreateTransferStatus.created)
    (failed := .linked_event_failed) (chain_open := .linked_event_chain_open)
    (on_fail := TigerBeetle.spend) (base := max s.prepare_timestamp s.now) (n := events.length)
    (fun s ts t h => h.create_transfer ts t) (fun _ _ _ h => h.spent)
    events 0 ⟨s, none, #[]⟩ ⟨h, by intro c hc; cases hc⟩
  exact this.1.congr rfl rfl rfl

/-! ## Expiry -/

theorem Server.Inv.expire {s : Server} (h : s.Inv) {ts : Time} {id : Id} {p : Transfer}
    (hp : (id, p) ∈ s.transfers) (hstat : get s.transfers_pending id = some .pending) :
    (s.expire ts id p).Inv := by
  unfold Server.expire
  split
  · rename_i dr cr hd hc
    exact h.complete rfl rfl rfl hp hstat (by simp) (by simp) rfl rfl hd hc rfl
      (Nat.le_add_right _ _) (Nat.le_refl _) (by (try dsimp only); split <;> rfl) rfl rfl
      (Nat.le_refl _) (by (try dsimp only); split <;> rfl)
  · exact h

theorem expire_transfers (s : Server) (ts : Time) (id : Id) (p : Transfer) :
    (s.expire ts id p).transfers = s.transfers := by
  unfold Server.expire; split <;> rfl

theorem expire_status (s : Server) (ts : Time) (id k : Id) (p : Transfer) (hk : id ≠ k) :
    get (s.expire ts id p).transfers_pending k = get s.transfers_pending k := by
  unfold Server.expire; split
  · exact get_put_of_ne hk
  · rfl

theorem Server.Inv.expire_all :
    ∀ (L : List (Id × Transfer)) (s : Server) (ts : Time), s.Inv →
      (∀ x ∈ L, x ∈ s.transfers ∧ get s.transfers_pending x.1 = some .pending) →
      (L.map (·.1)).Nodup → (s.expire_all ts L).Inv
  | [], s, _, h, _, _ => by unfold Server.expire_all; exact h
  | (id, p) :: rest, s, ts, h, hL, hnd => by
    unfold Server.expire_all
    have ⟨hp, hstat⟩ := hL (id, p) (List.mem_cons_self ..)
    have hnd' := List.nodup_cons.mp hnd
    refine Server.Inv.expire_all rest _ _ (h.expire hp hstat) ?_ hnd'.2
    intro x hx
    have ⟨hx1, hx2⟩ := hL x (List.mem_cons_of_mem _ hx)
    have hmem : x.1 ∈ rest.map (·.1) := List.mem_map_of_mem hx
    have hne : id ≠ x.1 := fun heq => hnd'.1 (by rw [heq]; exact hmem)
    exact ⟨by rw [expire_transfers]; exact hx1, by rw [expire_status _ _ _ _ _ hne]; exact hx2⟩

theorem Server.Inv.pulse {s : Server} (h : s.Inv) (lim : Limits) : (s.pulse lim).1.Inv := by
  unfold Server.pulse
  dsimp only
  split
  · exact h
  · refine (Server.Inv.expire_all _ _ _ h ?_ ?_).congr rfl rfl rfl
    · intro x hx
      have hx := List.mem_mergeSort.mp (List.mem_of_mem_take hx)
      have ⟨hx1, hx2⟩ := List.mem_filter.mp hx
      simp only [Bool.and_eq_true, beq_iff_eq] at hx2
      exact ⟨hx1, hx2.1⟩
    · refine List.Nodup.sublist ((List.take_sublist _ _).map _) ?_
      refine ((List.mergeSort_perm _ _).map _).nodup_iff.mpr ?_
      exact h.unique.sublist ((List.filter_sublist).map _)

/-! ## The model -/

theorem Server.Inv.external {s : Server} (h : s.Inv) (lim : Limits) (req : Request) :
    (s.external lim req).next.Inv := by
  cases req with
  | advance_clock => exact h.congr rfl rfl rfl
  | create_accounts events => exact h.create_accounts events
  | create_transfers events => exact h.create_transfers events
  | _ => exact h

theorem Server.Inv.internal {s : Server} (h : s.Inv) (lim : Limits) (w : Internal) :
    (s.internal lim w).next.Inv := by
  cases w; exact h.pulse lim

theorem Server.Inv.external_mem {lim : Limits} {s : Server} {r : Request}
    {o : Accordant.ExternalOutcome Server Response Internal Empty}
    (h : s.Inv) (ho : o ∈ (model lim).external r s) : Server.Inv o.next := by
  have ho := List.mem_singleton.mp ho; subst ho; exact h.external lim r

theorem Server.Inv.internal_mem {lim : Limits} {s : Server} {r : Internal}
    {o : Accordant.InternalOutcome Server Internal Empty}
    (h : s.Inv) (ho : o ∈ (model lim).internal r s) : Server.Inv o.next := by
  have ho := List.mem_singleton.mp ho; subst ho; exact h.internal lim r

theorem Server.Inv.step {lim : Limits} {c c' : Accordant.Config (model lim)}
    {l : Accordant.Label (model lim)} (hs : Accordant.Step (model lim) c l c')
    (h : Server.Inv c.state) : Server.Inv c'.state := by
  cases hs with
  | invoke => exact h
  | ret => exact h
  | receive => exact h
  | effect _ ho _ => exact h.external_mem ho
  | run _ _ ho _ => exact h.internal_mem ho

theorem Server.Inv.legal {lim : Limits} :
    ∀ {c : Accordant.Config (model lim)} {x : Accordant.Execution (model lim)},
      Server.Inv c.state → Accordant.Legal (model lim) c x → ∀ p ∈ x, Server.Inv p.2.state
  | _, [], _, _ => by simp
  | _, (_, _) :: _, h, ⟨hs, hrest⟩ => by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h.step hs
    · exact Server.Inv.legal (h.step hs) hrest p hp

/-! ## The theorem -/

/-- In every state TigerBeetle can reach, every account keeps the rule
    `debits_must_not_exceed_credits`: whatever runs, from an empty cluster, every
    account a lookup can return has `debits_pending + debits_posted ≤ credits_posted`
    if its flag is set. -/
theorem debits_must_not_exceed_credits (lim : Limits) (x : Accordant.Execution (model lim))
    (hx : Accordant.Legal (model lim) (Accordant.initial ({} : Server)) x) :
    ∀ p ∈ x, ∀ id a, get (p.2.state : Server).accounts id = some a →
      a.debits_must_not_exceed_credits :=
  fun p hp => (Server.Inv.legal Server.Inv.empty hx p hp).rule

end TigerBeetle

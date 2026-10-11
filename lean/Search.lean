import Accordant

/-!
# A checker, proved sound and complete

`Accordant.lean` says what a valid trace is and proves that checking a
certificate is enough. This file finds the certificate: a search over the
silent steps the trace doesn't show, with a proof in both directions.

```
theorem search_sound    : search m init k trace = some p → Valid m init trace
theorem search_complete : Runs m k (initial init) trace → (search m init k trace).isSome
theorem search_iff      : Valid m init trace ↔ ∃ k, (search m init k trace).isSome
```

`k` bounds the silent steps between two observed events; `Runs m k` is the
executions that respect it. Every execution respects some bound, so no valid
trace is missed for good: `search_iff`. For a fixed `k`, `none` means no
execution with at most `k` silent steps per gap explains the trace.

The search is the plain one: one frontier of configurations, every
interleaving explored. It is the reference the Rust checker refines
(footprints, partitions), and it runs: `#guard` at the bottom.
-/

namespace Accordant

variable {m : Model}

/-! ## Candidates: the silent moves a configuration offers -/

/-- Every pending external op, with every outcome. -/
def effects (c : Config m) : List Silent :=
  c.externals.flatMap fun o =>
    match o.res with
    | none => (List.range (m.external o.req c.state c.now).val.length).map (Silent.effect o.id)
    | some _ => []

/-- Every internal op, with every outcome. -/
def runs (c : Config m) : List Silent :=
  (List.range c.internals.length).flatMap fun i =>
    match c.internals[i]? with
    | some w => (List.range (m.internal w.req c.state c.now).length).map (Silent.run i)
    | none => []

def silents (c : Config m) : List Silent :=
  effects c ++ runs c

/-! ## The search -/

/-- A configuration and the moves that reached it, latest first. -/
abbrev Frontier (m : Model) := List (Config m × List (Move m))

/-- One silent step from every configuration. -/
def next (fr : Frontier m) : Frontier m :=
  fr.flatMap fun dp =>
    (silents dp.1).filterMap fun s =>
      (dp.1.move (.silent s)).map fun lc => (lc.2, .silent s :: dp.2)

/-- Up to `k` silent steps from every configuration. -/
def explore : Nat → Frontier m → Frontier m
  | 0, fr => fr
  | k + 1, fr => fr ++ explore k (next fr)

/-- The observed event, from every configuration that can make it. -/
def advance (e : m.Ev) (fr : Frontier m) : Frontier m :=
  fr.filterMap fun dp =>
    (dp.1.move (.obs e)).map fun lc => (lc.2, .obs e :: dp.2)

/-- The trace, event by event: at most `k` silent steps, then the event. -/
def run (k : Nat) : List m.Ev → Frontier m → Frontier m
  | [], fr => fr
  | e :: es, fr => run k es (advance e (explore k fr))

/-- An execution explaining the trace, as moves to replay, if the search finds
    one with at most `k` silent steps between events. -/
def search (m : Model) (init : m.State) (k : Nat) (trace : List m.Ev) : Option (List (Move m)) :=
  (run k trace [(initial init, [])]).head?.map fun dp => dp.2.reverse

/-! ## Soundness: what the search returns replays to the trace -/

/-- Where an execution from `c` ends. -/
def endOf (c : Config m) : Execution m → Config m
  | [] => c
  | (_, c') :: rest => endOf c' rest

theorem endOf_snoc (c : Config m) (ex : Execution m) (lc : Label m × Config m) :
    endOf c (ex ++ [lc]) = lc.2 := by
  induction ex generalizing c with
  | nil => rfl
  | cons x rest ih => exact ih x.2

theorem project_append (x y : Execution m) : project (x ++ y) = project x ++ project y := by
  induction x with
  | nil => rfl
  | cons lc rest ih => obtain ⟨l, c⟩ := lc; cases l <;> simp [project, ih]

theorem replay_snoc {c₀ : Config m} {p : List (Move m)} {ex : Execution m} {mv : Move m}
    {l : Label m} {c' : Config m}
    (h : replay c₀ p = some ex) (hm : (endOf c₀ ex).move mv = some (l, c')) :
    replay c₀ (p ++ [mv]) = some (ex ++ [(l, c')]) := by
  induction p generalizing c₀ ex with
  | nil =>
    simp only [replay, Option.some.injEq] at h
    subst h
    simp [replay, endOf] at hm ⊢
    simp [hm]
  | cons mv₁ rest ih =>
    simp only [replay] at h
    split at h
    · simp at h
    · rename_i l₁ c₁ hmv₁
      obtain ⟨ex', hex', rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [List.cons_append, replay, hmv₁]
      rw [ih hex' hm]
      rfl

/-- The label a move makes. -/
def Move.label : Move m → Label m
  | .obs e => .obs e
  | .silent _ => .silent

theorem move_label {c c' : Config m} {mv : Move m} {l : Label m}
    (h : c.move mv = some (l, c')) : l = mv.label := by
  cases mv with
  | obs e =>
    cases e <;> simp only [Config.move, Move.label] at h ⊢ <;>
      (repeat' split at h) <;> simp_all
  | silent s =>
    cases s <;> simp only [Config.move, Move.label] at h ⊢ <;>
      (repeat' split at h) <;> simp_all

/-- Every entry of the frontier replays to the trace so far and ends where it says. -/
def Good (init : m.State) (pre : List m.Ev) (fr : Frontier m) : Prop :=
  ∀ dp ∈ fr, ∃ ex, replay (initial init) dp.2.reverse = some ex ∧
    project ex = pre ∧ endOf (initial init) ex = dp.1

theorem next_good {init : m.State} {pre : List m.Ev} {fr : Frontier m}
    (h : Good init pre fr) : Good init pre (next fr) := by
  intro cp hcp
  simp only [next, List.mem_flatMap, List.mem_filterMap] at hcp
  obtain ⟨dp, hdp, s, _, hcp⟩ := hcp
  obtain ⟨ex, hre, hpr, hend⟩ := h dp hdp
  obtain ⟨⟨l, c'⟩, hmv, rfl⟩ := Option.map_eq_some_iff.mp hcp
  have hl := move_label hmv
  subst hl
  refine ⟨ex ++ [(Move.label (Move.silent s), c')], ?_, ?_, ?_⟩
  · rw [List.reverse_cons]; exact replay_snoc hre (hend ▸ hmv)
  · rw [project_append, hpr]; simp [project, Move.label]
  · exact endOf_snoc _ _ _

theorem explore_good {init : m.State} {pre : List m.Ev} {k : Nat}
    {fr : Frontier m} (h : Good init pre fr) : Good init pre (explore k fr) := by
  induction k generalizing fr with
  | zero => exact h
  | succ k ih =>
    intro dp hdp
    simp only [explore, List.mem_append] at hdp
    rcases hdp with hdp | hdp
    · exact h dp hdp
    · exact ih (next_good h) dp hdp

theorem advance_good {init : m.State} {pre : List m.Ev} {e : m.Ev}
    {fr : Frontier m} (h : Good init pre fr) : Good init (pre ++ [e]) (advance e fr) := by
  intro cp hcp
  simp only [advance, List.mem_filterMap] at hcp
  obtain ⟨dp, hdp, hcp⟩ := hcp
  obtain ⟨ex, hre, hpr, hend⟩ := h dp hdp
  obtain ⟨⟨l, c'⟩, hmv, rfl⟩ := Option.map_eq_some_iff.mp hcp
  have hl := move_label hmv
  subst hl
  refine ⟨ex ++ [(Move.label (Move.obs e), c')], ?_, ?_, ?_⟩
  · rw [List.reverse_cons]; exact replay_snoc hre (hend ▸ hmv)
  · rw [project_append, hpr]; simp [project, Move.label]
  · exact endOf_snoc _ _ _

theorem run_good {init : m.State} {pre : List m.Ev} {k : Nat}
    {es : List m.Ev} {fr : Frontier m} (h : Good init pre fr) :
    Good init (pre ++ es) (run k es fr) := by
  induction es generalizing pre fr with
  | nil => simpa [run] using h
  | cons e es ih =>
    simp only [run]
    have := ih (advance_good (e := e) (explore_good (k := k) h))
    simpa using this

/-- What the search returns replays to exactly the trace. -/
theorem search_replays {init : m.State} {k : Nat} {trace : List m.Ev} {p : List (Move m)}
    (h : search m init k trace = some p) :
    ∃ ex, replay (initial init) p = some ex ∧ project ex = trace := by
  simp only [search] at h
  obtain ⟨dp, hhead, rfl⟩ := Option.map_eq_some_iff.mp h
  have hmem : dp ∈ run k trace [(initial init, [])] :=
    List.mem_of_mem_head? (Option.mem_def.mpr hhead)
  have hgood : Good init [] [(initial init, [])] := by
    intro dp hdp
    simp only [List.mem_singleton] at hdp
    subst hdp
    exact ⟨[], rfl, rfl, rfl⟩
  obtain ⟨ex, hre, hpr, _⟩ := run_good (k := k) (es := trace) hgood dp hmem
  exact ⟨ex, hre, by simpa using hpr⟩

/-- Soundness: whatever the search finds is valid. -/
theorem search_sound {init : m.State} {k : Nat} {trace : List m.Ev} {p : List (Move m)}
    (h : search m init k trace = some p) : Valid m init trace := by
  obtain ⟨ex, hre, hpr⟩ := search_replays h
  exact ⟨ex, replay_legal hre, hpr⟩

/-! ## Completeness: the search finds every bounded execution -/

/-- `n` silent steps. -/
inductive SilentPath (m : Model) : Config m → Nat → Config m → Prop where
  | refl {c} : SilentPath m c 0 c
  | step {c c' c₁ n} : Step m c .silent c' → SilentPath m c' n c₁ → SilentPath m c (n + 1) c₁

/-- The trace can be run from `c` with at most `k` silent steps before each
    event. -/
inductive Runs (m : Model) (k : Nat) : Config m → List m.Ev → Prop where
  | nil {c} : Runs m k c []
  | step {c c₁ c₂ n e es} :
      SilentPath m c n c₁ → n ≤ k → Step m c₁ (.obs e) c₂ → Runs m k c₂ es → Runs m k c (e :: es)

theorem Runs.mono {k k' : Nat} {c : Config m} {es : List m.Ev} (hk : k ≤ k')
    (h : Runs m k c es) : Runs m k' c es := by
  induction h with
  | nil => exact .nil
  | step hp hn hs _ ih => exact .step hp (Nat.le_trans hn hk) hs ih

theorem Runs.silent_cons {k : Nat} {c c₁ : Config m} {es : List m.Ev}
    (hs : Step m c .silent c₁) (h : Runs m k c₁ es) : Runs m (k + 1) c es := by
  cases h with
  | nil => exact .nil
  | step hp hn hs' hr => exact .step (.step hs hp) (by omega) hs' (hr.mono (by omega))

/-- Every legal execution respects some bound: its own length. -/
theorem legal_runs {c : Config m} {x : Execution m} (h : Legal m c x) :
    Runs m x.length c (project x) := by
  induction x generalizing c with
  | nil => exact .nil
  | cons lc rest ih =>
    obtain ⟨l, c₁⟩ := lc
    obtain ⟨hstep, hrest⟩ := h
    cases l with
    | obs e => exact .step .refl (by simp) hstep ((ih hrest).mono (by simp))
    | silent => exact (ih hrest).silent_cons hstep

theorem valid_runs {init : m.State} {trace : List m.Ev} (h : Valid m init trace) :
    ∃ k, Runs m k (initial init) trace := by
  obtain ⟨x, hx, rfl⟩ := h
  exact ⟨x.length, legal_runs hx⟩

/-- Two configurations that differ only in the order of dispatches sent and not
    yet received. The semantics lets a client receive any of them; the search
    always removes the first, so it tracks a configuration up to this. -/
def Sim (c d : Config m) : Prop :=
  ∃ s, s.Perm c.sent ∧ d = { c with sent := s }

theorem Sim.refl (c : Config m) : Sim c c := ⟨c.sent, List.Perm.refl _, rfl⟩

theorem Sim.trans {c d e : Config m} (h₁ : Sim c d) (h₂ : Sim d e) : Sim c e := by
  obtain ⟨s, hs, rfl⟩ := h₁
  obtain ⟨t, ht, rfl⟩ := h₂
  exact ⟨t, ht.trans hs, rfl⟩

/-- A step from `c` has a matching step from anything `Sim` to it. -/
theorem step_sim {c d c' : Config m} {l : Label m} (hs : Sim c d) (h : Step m c l c') :
    ∃ d', Step m d l d' ∧ Sim c' d' := by
  obtain ⟨s, hperm, rfl⟩ := hs
  cases h with
  | invoke hf hov => exact ⟨_, .invoke hf hov, s, hperm, rfl⟩
  | ret hsplit hov => exact ⟨_, .ret hsplit hov, s, hperm, rfl⟩
  | receive hsent hov =>
    rename_i pre post msg
    have hmem : msg ∈ s := hperm.mem_iff.mpr (by rw [hsent]; simp)
    obtain ⟨pre', post', rfl⟩ := List.append_of_mem hmem
    refine ⟨_, .receive rfl hov, pre' ++ post', ?_, rfl⟩
    have h1 : (msg :: (pre' ++ post')).Perm (msg :: (pre ++ post)) :=
      (List.perm_middle.symm.trans hperm).trans (hsent ▸ List.perm_middle)
    exact h1.cons_inv
  | clock ht hov => exact ⟨_, .clock ht hov, s, hperm, rfl⟩
  | effect hsplit ho hov => exact ⟨_, .effect hsplit ho hov, _, hperm.append_right _, rfl⟩
  | run hw ha ho hf => exact ⟨_, .run hw ha ho hf, _, hperm.append_right _, rfl⟩

/-- Outstanding external ops have distinct ids: `invoke` only admits a fresh
    one. With it, the first op with an id is the op with that id. -/
def Uniq (c : Config m) : Prop := c.externals.Pairwise fun a b => a.id ≠ b.id

theorem uniq_sim {c d : Config m} (hu : Uniq c) (hs : Sim c d) : Uniq d := by
  obtain ⟨s, _, rfl⟩ := hs
  exact hu

theorem uniq_step {c c' : Config m} {l : Label m} (hu : Uniq c) (h : Step m c l c') : Uniq c' := by
  cases h with
  | invoke hf hov =>
    simp only [Uniq, List.pairwise_append, List.pairwise_cons, List.mem_singleton] at hu ⊢
    exact ⟨hu, ⟨by simp, List.Pairwise.nil⟩, fun a ha b hb => hb ▸ hf a ha⟩
  | ret hsplit hov =>
    rename_i pre post id req res
    simp only [Uniq, hsplit, List.pairwise_append, List.pairwise_cons] at hu ⊢
    obtain ⟨h1, ⟨_, h2⟩, h3⟩ := hu
    exact ⟨h1, h2, fun a ha b hb => h3 a ha b (List.mem_cons_of_mem _ hb)⟩
  | receive hsent hov => exact hu
  | clock ht hov => exact hu
  | effect hsplit ho hov =>
    rename_i pre post id req o
    simp only [Uniq, hsplit, List.pairwise_append, List.pairwise_cons] at hu ⊢
    obtain ⟨h1, ⟨h2, h3⟩, h4⟩ := hu
    refine ⟨h1, ⟨h2, h3⟩, fun a ha b hb => ?_⟩
    simp only [List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact h4 a ha ⟨id, req, none⟩ List.mem_cons_self
    · exact h4 a ha b (List.mem_cons_of_mem _ hb)
  | run hw ha ho hf => exact hu

theorem uniq_path {c c₁ : Config m} {n : Nat} (hu : Uniq c) (h : SilentPath m c n c₁) : Uniq c₁ := by
  induction h with
  | refl => exact hu
  | step hs _ ih => exact ih (uniq_step hu hs)

/-- With distinct ids, the op before which nothing matches is the one found. -/
theorem splitAt?_first {α : Type} {p : α → Bool} {pre post : List α} {x : α}
    (hpre : ∀ y ∈ pre, p y = false) (hx : p x = true) :
    splitAt? p (pre ++ x :: post) = some (pre, x, post) := by
  induction pre with
  | nil => simp [splitAt?, hx]
  | cons y ys ih =>
    have hy := hpre y (List.mem_cons_self)
    simp only [List.cons_append, splitAt?, hy, Bool.false_eq_true, ↓reduceIte]
    rw [ih (fun z hz => hpre z (List.mem_cons_of_mem _ hz))]
    rfl

theorem splitAt?_of_mem {α : Type} {p : α → Bool} {l : List α} {x : α}
    (hmem : x ∈ l) (hx : p x = true) : ∃ r, splitAt? p l = some r := by
  induction l with
  | nil => simp at hmem
  | cons y ys ih =>
    simp only [splitAt?]
    split
    · exact ⟨_, rfl⟩
    · rename_i hy
      have : x ∈ ys := by
        simp only [List.mem_cons] at hmem
        rcases hmem with rfl | h
        · exact absurd hx (by simpa using hy)
        · exact h
      obtain ⟨⟨pre, z, post⟩, hr⟩ := ih this
      exact ⟨(y :: pre, z, post), by simp [hr]⟩

theorem overdue_false {c : Config m} (h : ¬ c.overdue) : c.isOverdue = false := by
  cases hc : c.isOverdue with
  | false => rfl
  | true =>
    obtain ⟨w, hw, hwo⟩ := List.any_eq_true.mp hc
    exact absurd ⟨w, hw, isOverdue_iff.mp hwo⟩ h

theorem mayRun_of {c : Config m} {w : Sched m.Internal} (h : c.overdue → c.First w) :
    c.mayRun w = true := by
  unfold Config.mayRun
  by_cases hov : c.isOverdue = true
  · have hc : c.overdue := by
      obtain ⟨v, hv, hvo⟩ := List.any_eq_true.mp hov
      exact ⟨v, hv, isOverdue_iff.mp hvo⟩
    obtain ⟨hfirst, hall⟩ := h hc
    simp only [hov, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.all_eq_true]
    refine ⟨isOverdue_iff.mpr hfirst, fun v hv => ?_⟩
    by_cases hvo : v.isOverdue c = true
    · obtain ⟨d, e, hd, he, hde⟩ := hall v hv (isOverdue_iff.mp hvo)
      simp [dueLe, hd, he, hde]
    · simp [hvo]
  · simp [hov]

/-- Nothing before a pending op with a distinct id matches it. -/
theorem pending_first {pre : List (ExternalOp m)} {id : CallId}
    (h : ∀ y ∈ pre, y.id ≠ id) : ∀ y ∈ pre, pendingOp id y = false := by
  intro y hy
  simp [pendingOp, h y hy]

theorem settled_first {pre : List (ExternalOp m)} {id : CallId} {res : m.Response}
    (h : ∀ y ∈ pre, y.id ≠ id) : ∀ y ∈ pre, settledOp id res y = false := by
  intro y hy
  simp [settledOp, h y hy]

/-- Every silent step is one of the candidates, and `move` makes it exactly. -/
theorem silent_complete {c c' : Config m} (hu : Uniq c) (h : Step m c .silent c') :
    ∃ s ∈ silents c, c.move (.silent s) = some (.silent, c') := by
  cases h with
  | effect hsplit ho hov =>
    rename_i pre post id req o
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp ho
    have hpre : ∀ y ∈ pre, y.id ≠ id := by
      simp only [Uniq, hsplit, List.pairwise_append] at hu
      exact fun y hy => hu.2.2 y hy _ List.mem_cons_self
    have hsp : splitAt? (pendingOp id) c.externals = some (pre, ⟨id, req, none⟩, post) := by
      rw [hsplit]; exact splitAt?_first (pending_first hpre) (by simp [pendingOp])
    refine ⟨.effect id j, ?_, ?_⟩
    · apply List.mem_append_left
      simp only [effects, List.mem_flatMap]
      refine ⟨⟨id, req, none⟩, by rw [hsplit]; simp, ?_⟩
      simp only [List.mem_map, List.mem_range]
      exact ⟨j, (List.getElem?_eq_some_iff.mp hj).1, rfl⟩
    · simp [Config.move, hsp, hj, overdue_false hov]
  | run hw ha ho hf =>
    rename_i pre post w o
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp ho
    have hi : c.internals[pre.length]? = some w := by rw [hw]; simp
    refine ⟨.run pre.length j, ?_, ?_⟩
    · apply List.mem_append_right
      simp only [runs, List.mem_flatMap, List.mem_range]
      refine ⟨pre.length, by rw [hw]; simp, ?_⟩
      simp only [hi, List.mem_map, List.mem_range]
      exact ⟨j, (List.getElem?_eq_some_iff.mp hj).1, rfl⟩
    · simp only [Config.move, hi, hj, isReady_iff.mpr ha, mayRun_of hf, Bool.and_self, ↓reduceIte,
        Option.some.injEq, Prod.mk.injEq, true_and]
      rw [hw]
      simp [List.drop_append]

/-- Every observed step is made by `move`, up to the order of dispatches. -/
theorem obs_complete {c c' : Config m} {e : m.Ev} (hu : Uniq c) (h : Step m c (.obs e) c') :
    ∃ c'', c.move (.obs e) = some (.obs e, c'') ∧ Sim c' c'' := by
  cases h with
  | invoke hf hov =>
    have hall : c.externals.all (fun o => o.id != _) = true :=
      List.all_eq_true.mpr fun o ho => bne_iff_ne.mpr (hf o ho)
    exact ⟨_, by simp [Config.move, hall, overdue_false hov], Sim.refl _⟩
  | ret hsplit hov =>
    rename_i pre post id req res
    have hpre : ∀ y ∈ pre, y.id ≠ id := by
      simp only [Uniq, hsplit, List.pairwise_append] at hu
      exact fun y hy => hu.2.2 y hy _ List.mem_cons_self
    have hsp : splitAt? (settledOp id res) c.externals = some (pre, ⟨id, req, some res⟩, post) := by
      rw [hsplit]; exact splitAt?_first (settled_first hpre) (by simp [settledOp])
    exact ⟨_, by simp [Config.move, hsp, overdue_false hov], Sim.refl _⟩
  | receive hsent hov =>
    rename_i pre post msg
    have hmem : msg ∈ c.sent := by rw [hsent]; simp
    obtain ⟨⟨pre', d, post'⟩, hsp⟩ :=
      splitAt?_of_mem (p := fun d => @decide (d = msg) (m.decEqDispatch d msg)) hmem (by simp)
    obtain ⟨h1, h2⟩ := splitAt?_spec hsp
    have : d = msg := by simpa using h2
    subst this
    refine ⟨_, by simp [Config.move, hsp, overdue_false hov], pre' ++ post', ?_, rfl⟩
    have : (d :: (pre' ++ post')).Perm (d :: (pre ++ post)) :=
      (List.perm_middle.symm.trans (h1 ▸ hsent ▸ List.Perm.refl _)).trans List.perm_middle
    exact this.cons_inv
  | clock ht hov =>
    exact ⟨_, by simp [Config.move, ht, overdue_false hov], Sim.refl _⟩

theorem mem_explore_self {k : Nat} {fr : Frontier m} {dp : Config m × List (Move m)}
    (h : dp ∈ fr) : dp ∈ explore k fr := by
  cases k with
  | zero => exact h
  | succ k => exact List.mem_append_left _ h

theorem explore_complete {c c₁ : Config m} {n k : Nat} {fr : Frontier m}
    (hp : SilentPath m c n c₁) (hn : n ≤ k) (hu : Uniq c)
    (hfr : ∃ dp ∈ fr, Sim c dp.1) : ∃ dp ∈ explore k fr, Sim c₁ dp.1 := by
  induction hp generalizing k fr with
  | refl =>
    obtain ⟨dp, hdp, hs⟩ := hfr
    exact ⟨dp, mem_explore_self hdp, hs⟩
  | step hstep hpath ih =>
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨dp, hdp, hs⟩ := hfr
    obtain ⟨d', hd', hs'⟩ := step_sim hs hstep
    obtain ⟨s, hsm, hmv⟩ := silent_complete (uniq_sim hu hs) hd'
    have hmem : (d', .silent s :: dp.2) ∈ next fr := by
      simp only [next, List.mem_flatMap, List.mem_filterMap]
      exact ⟨dp, hdp, s, hsm, by simp [hmv]⟩
    obtain ⟨dp₁, h1, h2⟩ := ih (k := k') (by omega) (uniq_step hu hstep) ⟨_, hmem, hs'⟩
    exact ⟨dp₁, List.mem_append_right _ h1, h2⟩

theorem run_complete {k : Nat} {c : Config m} {es : List m.Ev} {fr : Frontier m}
    (hr : Runs m k c es) (hu : Uniq c) (hfr : ∃ dp ∈ fr, Sim c dp.1) : run k es fr ≠ [] := by
  induction hr generalizing fr with
  | nil =>
    obtain ⟨dp, hdp, _⟩ := hfr
    exact List.ne_nil_of_mem hdp
  | @step _ _ _ _ e _ hp hn hs _ ih =>
    obtain ⟨dp, hdp, hsim⟩ := explore_complete hp hn hu hfr
    have hu₁ := uniq_path hu hp
    obtain ⟨d₂, hd₂, hs₂⟩ := step_sim hsim hs
    obtain ⟨d₂', hmv, hs₂'⟩ := obs_complete (uniq_sim hu₁ hsim) hd₂
    have hmem : (d₂', .obs e :: dp.2) ∈ advance e (explore k fr) := by
      simp only [advance, List.mem_filterMap]
      exact ⟨dp, hdp, by simp [hmv]⟩
    exact ih (uniq_step hu₁ hs) ⟨_, hmem, hs₂.trans hs₂'⟩

/-- Completeness: every execution with at most `k` silent steps between events
    is found. -/
theorem search_complete {init : m.State} {k : Nat} {trace : List m.Ev}
    (h : Runs m k (initial init) trace) : (search m init k trace).isSome := by
  have hne := run_complete (fr := [(initial init, [])]) h List.Pairwise.nil
    ⟨_, List.mem_singleton_self _, Sim.refl _⟩
  simp only [search]
  cases hrun : run k trace [(initial init, [])] with
  | nil => exact absurd hrun hne
  | cons dp rest => rfl

/-- Both directions: a trace is valid exactly when the search finds it with
    some bound. -/
theorem search_iff {init : m.State} {trace : List m.Ev} :
    Valid m init trace ↔ ∃ k, (search m init k trace).isSome := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := valid_runs h
    exact ⟨k, search_complete hk⟩
  · rintro ⟨k, hk⟩
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hk
    exact search_sound hp

/-! ## It runs

`#guard` evaluates the search; the build fails if a line is wrong. -/

-- The counter: sent, then answered 1. One silent step, the effect.
#guard (search counter 0 1 [.invoke 7 (), .ret 7 1]).isSome
-- Answered 2: no execution explains it.
#guard !(search counter 0 1 [.invoke 7 (), .ret 7 2]).isSome
-- Two concurrent increments: either may take effect first.
#guard (search counter 0 2 [.invoke 1 (), .invoke 2 (), .ret 2 1, .ret 1 2]).isSome
#guard (search counter 0 2 [.invoke 1 (), .invoke 2 (), .ret 2 2, .ret 1 1]).isSome
-- Both answered 2: impossible.
#guard !(search counter 0 2 [.invoke 1 (), .invoke 2 (), .ret 2 2, .ret 1 2]).isSome
-- With no silent steps allowed, nothing can take effect.
#guard !(search counter 0 0 [.invoke 7 (), .ret 7 1]).isSome
-- A call id is in use until its return.
#guard !(search counter 0 2 [.invoke 7 (), .invoke 7 ()]).isSome

/-- A counter with a timer: `arm` sets a timer at 5 that resets the count. -/
abbrev timed : Model where
  State    := Nat
  External := Bool          -- true: increment; false: arm the timer
  Response := Nat
  Internal := Unit
  Dispatch := Empty
  external := fun req n _ => if req then .one ⟨n + 1, n + 1, [], []⟩ else .one ⟨n, n, [.timer 5 ()], []⟩
  internal := fun _ _ _ => [⟨0, [], []⟩]

-- Arm, increment, the clock passes 5, increment: the timer reset the count.
#guard (search timed 0 2 [.invoke 1 false, .ret 1 0, .invoke 2 true, .ret 2 1, .clock 9, .invoke 3 true, .ret 3 1]).isSome
-- Without the reset the count would be 2: not explained.
#guard !(search timed 0 2 [.invoke 1 false, .ret 1 0, .invoke 2 true, .ret 2 1, .clock 9, .invoke 3 true, .ret 3 2]).isSome
-- The timer can't fire before 5.
#guard !(search timed 0 2 [.invoke 1 false, .ret 1 0, .invoke 2 true, .ret 2 1, .clock 4, .invoke 3 true, .ret 3 1]).isSome
-- The clock doesn't move back.
#guard !(search timed 0 2 [.clock 9, .clock 4]).isSome

end Accordant

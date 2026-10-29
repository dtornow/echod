import Exp2.SystemRefinement
import Experiment.PromiseFrame

/-!
# Storage simulation facts

The global abstract state is related to the object store extensionally, by
promise id. A node computes on one loaded document; `request_transport`
lifts that outcome to the global state without depending on list order.
-/

namespace Exp2

open Experiment
open Experiment.Storage

structure Call where
  client : Addr
  id     : CallId
  req    : Request
  now    : Time

def Call.retry (call : Call) (tries : Nat) :
    (k : Nat) → k < tries → NodeP Unit :=
  fun k _ => serve call.client call.id call.req call.now k

def Candidate.call (cand : Candidate) : Call :=
  ⟨cand.client, cand.id, cand.req, cand.now⟩

inductive Control : Running Storage.Config Nat CMsg → Prop where
  | idle {next mailbox} :
      take? isRequest mailbox = none →
      Control ⟨next, mailbox, node⟩
  | loading {call : Call} {tries op next mailbox k} :
      next = op + 1 →
      k = loadK tries (call.retry tries) call.client call.id call.req call.now op →
      take? (answers op) mailbox = none →
      Control ⟨next, mailbox, k⟩
  | writing {cand : Candidate} {op next mailbox k} :
      next = op + 1 →
      k = writeK cand.tries (cand.call.retry cand.tries) cand op →
      take? (answers op) mailbox = none →
      Control ⟨next, mailbox, k⟩

theorem initial_control : Control (⟨0, [], node⟩ : Running Storage.Config Nat CMsg) :=
  .idle rfl

def storeLookup (s : Store) (key : Ident) : Option (Promise × Version) :=
  (s.docs.find? (·.1 == key)).map fun (_, p, v) => (p, v)

def storePromiseAt (s : Store) (key : Ident) : Option Promise :=
  (storeLookup s key).map (·.1)

def StoreRep (store : Store) (state : Experiment.State) : Prop :=
  ∀ key, storePromiseAt store key = Experiment.promiseAt state key

def storeCommit (store : Store) (key : Ident) (p : Promise) : Store :=
  let version := (storeLookup store key).map (·.2) |>.getD 0
  { docs := (key, p, version + 1) :: store.docs.filter (·.1 != key) }

theorem find?_filter_store_other (docs : List (Ident × Promise × Version))
    {keep drop : Ident} (h : keep ≠ drop) :
    (docs.filter (·.1 != drop)).find? (·.1 == keep) = docs.find? (·.1 == keep) := by
  induction docs with
  | nil => rfl
  | cons entry rest ih =>
    simp only [List.filter_cons, List.find?_cons]
    by_cases hd : entry.1 = drop
    · have hk : entry.1 ≠ keep := by
        intro he
        exact h (he.symm.trans hd)
      rw [show (entry.1 != drop) = false from bne_eq_false_iff_eq.mpr hd]
      rw [show (entry.1 == keep) = false from beq_eq_false_iff_ne.mpr hk]
      simp only [Bool.false_eq_true, if_false]
      exact ih
    · rw [show (entry.1 != drop) = true from bne_iff_ne.mpr hd]
      change (entry :: rest.filter (·.1 != drop)).find? (·.1 == keep) =
        (entry :: rest).find? (·.1 == keep)
      by_cases hk : entry.1 = keep
      · rw [List.find?_cons, List.find?_cons,
          show (entry.1 == keep) = true from beq_iff_eq.mpr hk]
      · rw [List.find?_cons, List.find?_cons,
          show (entry.1 == keep) = false from beq_eq_false_iff_ne.mpr hk]
        exact ih

theorem storePromiseAt_commit (store : Store) (key : Ident) (p : Promise) (other : Ident) :
    storePromiseAt (storeCommit store key p) other =
      if other = key then some p else storePromiseAt store other := by
  by_cases h : other = key
  · subst other
    simp [storePromiseAt, storeLookup, storeCommit]
  · simp only [storePromiseAt, storeLookup, storeCommit, List.find?_cons]
    rw [show (key == other) = false from beq_eq_false_iff_ne.mpr (Ne.symm h)]
    rw [if_neg h]
    simp only
    rw [find?_filter_store_other _ h]

def Candidate.Valid (cfg : Storage.Config) (cand : Candidate) : Prop :=
  let before : Experiment.State := { promises := cand.doc.toList.map (·.1) }
  (cand.res, cand.after, cand.outs) =
      pick ((Experiment.request cand.req cand.now).run
        { cfg.app with unreliable := true } before) 0 ∧
  cand.after.promises.find? (·.id == cand.req.key) = some cand.promise ∧
  cand.after.promises = [cand.promise]

theorem Candidate.local_member {cfg : Storage.Config} {cand : Candidate}
    (h : cand.Valid cfg) :
    (cand.res, cand.after, cand.outs) ∈
      ((Experiment.request cand.req cand.now).run
        { cfg.app with unreliable := true }
        { promises := cand.doc.toList.map (·.1) }).val := by
  rw [h.1]
  exact pick_mem _ _

theorem Candidate.promise_id {cfg : Storage.Config} {cand : Candidate}
    (h : cand.Valid cfg) : cand.promise.id = cand.req.key := by
  have hf := List.find?_some h.2.1
  exact beq_iff_eq.mp hf

theorem storeAt_of_lookup {store : Store} {key : Ident}
    {doc : Option (Promise × Version)} (h : storeLookup store key = doc) :
    storePromiseAt store key = doc.map (·.1) := by
  simp [storePromiseAt, h]

/-- A valid candidate computed from the store's current document is an
abstract handler step on the represented global state. -/
theorem candidate_transport {cfg : Storage.Config} {cand : Candidate}
    {store : Store} {global : Experiment.State}
    (hrep : StoreRep store global)
    (hdoc : storeLookup store cand.req.key = cand.doc)
    (hcand : cand.Valid cfg) :
    ∃ globalAfter,
      (cand.res, globalAfter, cand.outs) ∈
        ((Experiment.request cand.req cand.now).run
          { cfg.app with unreliable := true } global).val ∧
      SameState
        (cand.after.withFrame (global.promises.filter (·.id != cand.req.key)))
        globalAfter := by
  have hglobalDoc : Experiment.promiseAt global cand.req.key =
      cand.doc.map (·.1) := by
    rw [← hrep cand.req.key]
    exact storeAt_of_lookup hdoc
  exact request_transport cand.req cand.now
    { cfg.app with unreliable := true } global cand.after
    (cand.doc.map (·.1)) cand.res cand.outs hglobalDoc
    (by
      have hm := Candidate.local_member hcand
      cases h : cand.doc with
      | none =>
        simp only [h, Option.toList, List.map_nil, Option.map] at hm ⊢
        change (cand.res, cand.after, cand.outs) ∈
          (Experiment.request cand.req cand.now
            { cfg.app with unreliable := true } {}).val at hm
        exact hm
      | some value =>
        simp only [h, Option.toList, List.map_cons, List.map_nil, Option.map] at hm ⊢
        change (cand.res, cand.after, cand.outs) ∈
          (Experiment.request cand.req cand.now
            { cfg.app with unreliable := true } { promises := [value.1] }).val at hm
        exact hm)

/-- Committing the candidate document preserves the extensional store/state
representation established by `candidate_transport`. -/
theorem commit_rep {cfg : Storage.Config} {cand : Candidate}
    {store : Store} {global globalAfter : Experiment.State}
    (hcand : cand.Valid cfg)
    (hrep : StoreRep store global)
    (hstate : SameState
      (cand.after.withFrame (global.promises.filter (·.id != cand.req.key)))
      globalAfter) :
    StoreRep (storeCommit store cand.req.key cand.promise) globalAfter := by
  intro key
  rw [storePromiseAt_commit]
  by_cases hk : key = cand.req.key
  · subst key
    rw [if_pos rfl, ← hstate cand.req.key]
    have hp := Candidate.promise_id hcand
    simp [Experiment.promiseAt, State.withFrame, hcand.2.2, hp]
  · rw [if_neg hk, ← hstate key]
    have hp := Candidate.promise_id hcand
    have hpk : cand.promise.id ≠ key := by
      intro he
      exact hk (he.symm.trans hp)
    simp only [Experiment.promiseAt, State.withFrame, hcand.2.2,
      List.singleton_append, List.find?_cons]
    rw [show (cand.promise.id == key) = false from beq_eq_false_iff_ne.mpr hpk]
    rw [Experiment.find?_filter_other _ hk]
    exact hrep key

end Exp2

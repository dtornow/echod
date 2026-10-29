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

def storeLookup (s : Store) (key : Ident) : Option (Promise × Version) :=
  (s.docs.find? (·.1 == key)).map fun (_, p, v) => (p, v)

def storePromiseAt (s : Store) (key : Ident) : Option Promise :=
  (storeLookup s key).map (·.1)

def StoreRep (store : Store) (state : Experiment.State) : Prop :=
  ∀ key, storePromiseAt store key = Experiment.promiseAt state key

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

end Exp2

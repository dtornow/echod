import Resonate.Concrete

/-!
# Facts retained for the narrow promise-slice store

The former end-to-end theorem related a one-document promise handler to this
store. Full Resonate transitions can atomically touch several fused objects,
schedules, and emit boundary messages, while this wire protocol carries
exactly one promise document. There is therefore no state representation
relation under which that old theorem states full-protocol refinement. The raw
PUT facts are kept here without widening their claim.
-/

namespace Resonate.PromiseSlice.Refinement

open Concrete

theorem committed_version (store : Store) (key : Key) (document : Promise) :
    (store.commit key document).version key =
      some ((store.version key).getD 0 + 1) := by
  simp [Store.commit, Store.version, Store.document]

/-- Replaying an absent-version conditional PUT after it landed conflicts. -/
theorem duplicate_absent_put_conflicts (key : Key) (document : Promise) :
    (Concrete.put {} (Concrete.Store.commit {} key document)
      key document none).val =
      [({ store := Concrete.Store.commit {} key document,
          reply := .conflict } : Concrete.PutResult)] := by
  simp [Concrete.put, Store.commit, Store.version, Store.document,
    Rover.Outcomes.one]

/-- The precise reason the old boundary theorem is intentionally scoped out. -/
def fullRefinementBlocker : String :=
  "the concrete wire store writes one legacy promise document, but a full " ++
  "Resonate handler may atomically update multiple fused promise/task rows, " ++
  "schedules, and emit boundary messages"

end Resonate.PromiseSlice.Refinement

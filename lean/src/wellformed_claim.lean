import wellformed_proof
import refinement_claim

namespace Resonate

open Rover

/-- Every valid trace of the concrete model, at every step: every document the
store holds is well-formed. The initial store is empty. -/
theorem documents_stay_well_formed
    (abstractConfig : Abstract.Config)
    (concreteConfig : Concrete.Config)
    (nodes : List Addr)
    (trace : Trace (Concrete.model nodes abstractConfig))
    (h : ValidTrace (Concrete.model nodes abstractConfig) concreteConfig trace) :
    ∀ entry ∈ trace, Concrete.Formed entry.2 :=
  fun entry hentry _ hstore =>
    Concrete.reachable_store_well_formed (h.reachable entry hentry) hstore

end Resonate

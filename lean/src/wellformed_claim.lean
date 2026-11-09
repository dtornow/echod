import wellformed_proof

namespace Resonate

open Rover

/-- Every behavior of the concrete model, at every step: every document the
store holds is well-formed. The initial store is empty. -/
theorem documents_stay_well_formed
    (appConfig : Resonate.Config)
    (concreteConfig : Concrete.Config)
    (nodes : List Addr)
    (execution : Execution (Concrete.model nodes appConfig))
    (hbehavior : Behavior (Concrete.model nodes appConfig) concreteConfig execution) :
    ∀ entry ∈ execution, Concrete.Formed entry.2 :=
  fun entry hentry _ hstore =>
    Concrete.reachable_store_well_formed (hbehavior.reachable entry hentry) hstore

end Resonate

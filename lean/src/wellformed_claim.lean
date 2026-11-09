import wellformed_proof

namespace Resonate

/-- In every reachable concrete system, every document the store holds is
well-formed: its promise, task, and schedule rows satisfy the catalogue in
`concrete.WellFormed`. -/
theorem documents_stay_well_formed
    (appConfig : Resonate.Config)
    (concreteConfig : Concrete.Config)
    (nodes : List Addr)
    (system : Rover.System (Concrete.model nodes appConfig))
    (hreachable : Rover.Reachable (Concrete.model nodes appConfig) concreteConfig system)
    (store : Concrete.Store)
    (hstore : system.process .store = .store store) :
    store.WellFormed :=
  Concrete.reachable_store_well_formed hreachable hstore

end Resonate

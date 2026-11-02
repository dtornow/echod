import «concrete».Refinement

namespace Resonate

theorem boundary_refinement
    (nodes : List Addr) (appConfig : Config)
    (config : Concrete.Config) (events : List BoundaryEvent) :
    Concrete.ValidBoundaryTrace nodes appConfig config events →
    Abstract.ValidBoundaryTrace
      { appConfig with unreliable := true } events :=
  Refinement.boundary_refinement_proof events

end Resonate

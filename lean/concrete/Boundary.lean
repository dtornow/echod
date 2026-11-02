import «concrete».Refinement

namespace Resonate

theorem concrete_refines_abstract
    (nodes : List Addr) (appConfig : Config)
    (config : Concrete.Config) (events : List BoundaryEvent) :
    Concrete.ValidBoundaryTrace nodes appConfig config events →
    Abstract.ValidBoundaryTrace
      { appConfig with unreliable := true } events :=
  Refinement.refinement_proof events

end Resonate

import «concrete».Refinement

namespace Resonate

abbrev ExternalTrace := BoundaryEvent

abbrev Concrete.ValidExternalTrace := Concrete.ValidBoundaryTrace

abbrev Abstract.ValidExternalTrace := Abstract.ValidBoundaryTrace

theorem concrete_refines_abstract
    (nodes : List Addr) (appConfig : Config)
    (config : Concrete.Config) (events : List ExternalTrace) :
    Concrete.ValidExternalTrace nodes appConfig config events →
    Abstract.ValidExternalTrace
      { appConfig with unreliable := true } events :=
  Refinement.refinement_proof events

end Resonate

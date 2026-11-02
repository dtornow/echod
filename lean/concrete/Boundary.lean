import «concrete».Refinement

namespace Resonate

abbrev ExternalTrace := BoundaryEvent

abbrev Concrete.ValidExternalTrace := Concrete.ValidBoundaryTrace

abbrev Abstract.ValidExternalTrace := Abstract.ValidBoundaryTrace

abbrev Abstract.Config : Type := _root_.Resonate.Config

theorem concrete_refines_abstract
    (nodes : List Addr)
    (abstractConfig : Abstract.Config)
    (concreteConfig : Concrete.Config)
    (events : List ExternalTrace) :
    Concrete.ValidExternalTrace nodes abstractConfig concreteConfig events →
    Abstract.ValidExternalTrace
      { abstractConfig with unreliable := true } events :=
  Refinement.refinement_proof events

end Resonate

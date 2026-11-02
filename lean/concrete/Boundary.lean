import «concrete».Refinement

namespace Resonate

abbrev ExternalTrace := BoundaryEvent

namespace Concrete

abbrev ValidExternalTrace
    (abstractConfig : _root_.Resonate.Config)
    (concreteConfig : Config) (nodes : List Addr)
    (trace : List _root_.Resonate.ExternalTrace) : Prop :=
  ValidBoundaryTrace nodes abstractConfig concreteConfig trace

end Concrete

abbrev Abstract.ValidExternalTrace := Abstract.ValidBoundaryTrace

abbrev Abstract.Config : Type := _root_.Resonate.Config

theorem concrete_refines_abstract
    (abstractConfig : Abstract.Config)
    (concreteConfig : Concrete.Config)
    (nodes : List Addr)
    (trace : List ExternalTrace) :
    Concrete.ValidExternalTrace abstractConfig concreteConfig nodes trace →
    Abstract.ValidExternalTrace abstractConfig trace :=
  Refinement.refinement_proof trace

end Resonate

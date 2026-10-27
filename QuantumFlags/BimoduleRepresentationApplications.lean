import QuantumFlags.BimoduleRepresentationEquivalence

namespace QuantumFlags
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
variable (N : DivisionBimodule.{u})

theorem bimoduleTensorRepresentation_action (M : TensorRepresentation N)
    (r : (BimoduleTriangularRing N)ᵐᵒᵖ) (p : M.Source × M.Target) :
    letI := bimoduleModuleFromHomRepresentation N (tensorRepresentationToHom M)
    r • p = ((bimoduleSourceHom N).op r • p.1,
      M.arrow (balancedPure N M.Source p.1 (bimoduleCrossHom N r.unop)) +
        (bimoduleTargetHom N).op r • p.2) := rfl

instance bimoduleModuleHasBinaryProducts :
    HasBinaryProducts (ModuleCat.{max u v} (BimoduleTriangularRing N)ᵐᵒᵖ) :=
  Adjunction.hasLimitsOfShape_of_equivalence (bimoduleRepresentationEquivalence N).inverse

instance bimoduleModuleHasBinaryBiproducts :
    HasBinaryBiproducts (ModuleCat.{max u v} (BimoduleTriangularRing N)ᵐᵒᵖ) :=
  HasBinaryBiproducts.of_hasBinaryProducts

theorem bimoduleRepresentation_indecomposable_iff
    (M : HomRepresentation.{u, max u v, max u v} N) :
    Indecomposable ((bimoduleRepresentationEquivalence N).functor.obj M) ↔ Indecomposable M :=
  equivalence_indecomposable_iff (bimoduleRepresentationEquivalence N) M

theorem bimoduleTensorRepresentation_indecomposable_iff
    (M : TensorRepresentation.{u, max u v, max u v} N) :
    Indecomposable ((bimoduleTensorRepresentationEquivalence N).functor.obj M) ↔ Indecomposable M :=
  equivalence_indecomposable_iff (bimoduleTensorRepresentationEquivalence N) M

def bimoduleRepresentationEndRingEquiv (M : HomRepresentation.{u, max u v, max u v} N) :
    End M ≃+* End ((bimoduleRepresentationEquivalence N).functor.obj M) where
  toEquiv := (bimoduleRepresentationEquivalence N).fullyFaithfulFunctor.homEquiv
  map_mul' f g := (bimoduleRepresentationEquivalence N).functor.map_comp g f
  map_add' f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro p
    rfl

theorem bimoduleRepresentationEndRingEquiv_exists
    (M : HomRepresentation.{u, max u v, max u v} N) :
    Nonempty (End M ≃+* End ((bimoduleRepresentationEquivalence N).functor.obj M)) :=
  ⟨bimoduleRepresentationEndRingEquiv N M⟩

def bimoduleTensorRepresentationEndRingEquiv (M : TensorRepresentation.{u, max u v, max u v} N) :
    End M ≃+* End ((bimoduleTensorRepresentationEquivalence N).functor.obj M) where
  toEquiv := (bimoduleTensorRepresentationEquivalence N).fullyFaithfulFunctor.homEquiv
  map_mul' f g := (bimoduleTensorRepresentationEquivalence N).functor.map_comp g f
  map_add' f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro p
    rfl

theorem bimoduleTensorRepresentationEndRingEquiv_exists
    (M : TensorRepresentation.{u, max u v, max u v} N) :
    Nonempty (End M ≃+* End ((bimoduleTensorRepresentationEquivalence N).functor.obj M)) :=
  ⟨bimoduleTensorRepresentationEndRingEquiv N M⟩

end
end QuantumFlags

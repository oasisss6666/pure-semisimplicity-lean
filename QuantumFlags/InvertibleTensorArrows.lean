import QuantumFlags.TensorRepresentationCategory
import QuantumFlags.RepresentationSplitBiproduct
import QuantumFlags.EquivalenceIndecomposable

namespace QuantumFlags
noncomputable section
open CategoryTheory
universe u v
variable {N : DivisionBimodule.{u}}
variable {M P Q : TensorRepresentation.{u,max u v,max u v} N}

def invertibleTensorArrowMorphism (hM : Function.Bijective M.arrow)
    (f : M.Source →ₗ[N.LeftRingᵐᵒᵖ] P.Source) : M ⟶ P where
  source := f
  target := P.arrow.comp ((balancedTensorMap N M.Source f).comp
    (LinearEquiv.ofBijective M.arrow hM).symm.toLinearMap)
  commutes z := by
    change P.arrow (balancedTensorMap N M.Source f z) =
      P.arrow (balancedTensorMap N M.Source f ((LinearEquiv.ofBijective M.arrow hM).symm ((LinearEquiv.ofBijective M.arrow hM) z)))
    rw [LinearEquiv.symm_apply_apply]

theorem invertibleTensorArrowMorphism_ext (hM : Function.Surjective M.arrow)
    {f g : M ⟶ P} (hs : f.source = g.source) : f = g := by
  apply TensorRepresentationMorphism.ext hs
  apply LinearMap.ext; intro y
  obtain ⟨z,rfl⟩ := hM y
  rw [← f.commutes, ← g.commutes, hs]

theorem invertibleTensorArrowMorphism_comp
    (hM : Function.Bijective M.arrow) (hP : Function.Bijective P.arrow)
    (f : M.Source →ₗ[N.LeftRingᵐᵒᵖ] P.Source)
    (g : P.Source →ₗ[N.LeftRingᵐᵒᵖ] Q.Source) :
    invertibleTensorArrowMorphism hM f ≫ invertibleTensorArrowMorphism hP g =
      invertibleTensorArrowMorphism hM (g.comp f) := by
  apply invertibleTensorArrowMorphism_ext hM.surjective
  rfl

theorem invertibleTensorArrowMorphism_identity (hM : Function.Bijective M.arrow) :
    invertibleTensorArrowMorphism hM LinearMap.id = 𝟙 M := by
  apply invertibleTensorArrowMorphism_ext hM.surjective
  rfl

theorem indecomposable_tensor_retract_isomorphism
    (hM : Indecomposable M) (hP : ¬ CategoryTheory.Limits.IsZero P)
    (i : P ⟶ M) (p : M ⟶ P) (hpi : i ≫ p = 𝟙 P) : Nonempty (M ≅ P) := by
  let E := tensorHomCategoryEquivalence N
  have hM' : Indecomposable (E.functor.obj M) :=
    (equivalence_indecomposable_iff E M).mpr hM
  have hP' : ¬ CategoryTheory.Limits.IsZero (E.functor.obj P) := by
    intro hz
    exact hP ((equivalence_isZero_iff E P).mp hz)
  obtain ⟨e⟩ := indecomposable_retract_isomorphism hM' hP'
    (E.functor.map i) (E.functor.map p) (by rw [← Functor.map_comp, hpi]; exact E.functor.map_id P)
  exact ⟨E.fullyFaithfulFunctor.preimageIso e⟩

end
end QuantumFlags

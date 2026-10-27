import QuantumFlags.SimpleIndecomposable
import QuantumFlags.RepresentationSplitBiproduct

namespace QuantumFlags
noncomputable section
open CategoryTheory
universe u v
variable (N : DivisionBimodule.{u})

theorem indecomposable_homArrow_injective (M : HomRepresentation.{u,max u v,max u v} N)
    (hM : Indecomposable M) (hS : ¬ Nonempty (M ≅ simpleSource.{u,v} N)) :
    Function.Injective M.arrow := by
  apply (no_simpleSourceSummand_iff_injective N M).mp
  rintro ⟨i,p,hpi⟩
  exact hS (indecomposable_retract_isomorphism hM (simpleSource_indecomposable N).1 i p hpi)

theorem indecomposable_homTensorArrow_surjective (M : HomRepresentation.{u,max u v,max u v} N)
    (hM : Indecomposable M) (hT : ¬ Nonempty (M ≅ simpleTarget.{u,v} N)) :
    Function.Surjective (homRepresentationToTensor M).arrow := by
  apply (no_simpleTargetSummand_iff_surjective N M).mp
  rintro ⟨i,p,hpi⟩
  exact hT (indecomposable_retract_isomorphism hM (simpleTarget_indecomposable N).1 i p hpi)

theorem indecomposable_tensorAdjoint_injective (M : TensorRepresentation.{u,max u v,max u v} N)
    (hM : Indecomposable M) (hS : ¬ Nonempty (M ≅ tensorSimpleSource.{u,v} N)) :
    Function.Injective (tensorRepresentationToHom M).arrow := by
  apply indecomposable_homArrow_injective N (tensorRepresentationToHom M)
    ((equivalence_indecomposable_iff (tensorHomCategoryEquivalence N) M).mpr hM)
  rintro ⟨α⟩
  exact hS ⟨(tensorHomCategoryEquivalence N).fullyFaithfulFunctor.preimageIso α⟩

theorem indecomposable_tensorArrow_surjective (M : TensorRepresentation.{u,max u v,max u v} N)
    (hM : Indecomposable M) (hT : ¬ Nonempty (M ≅ tensorSimpleTarget.{u,v} N)) :
    Function.Surjective M.arrow := by
  have h := indecomposable_homTensorArrow_surjective N (tensorRepresentationToHom M)
    ((equivalence_indecomposable_iff (tensorHomCategoryEquivalence N) M).mpr hM) (by
      rintro ⟨α⟩
      exact hT ⟨(tensorHomCategoryEquivalence N).fullyFaithfulFunctor.preimageIso α⟩)
  rwa [tensorHom_arrow_roundtrip] at h

theorem indecomposable_nonsimple_tensor_arrows (M : TensorRepresentation.{u,max u v,max u v} N)
    (hM : Indecomposable M) (hS : ¬ Nonempty (M ≅ tensorSimpleSource.{u,v} N))
    (hT : ¬ Nonempty (M ≅ tensorSimpleTarget.{u,v} N)) :
    Function.Injective (tensorRepresentationToHom M).arrow ∧ Function.Surjective M.arrow :=
  ⟨indecomposable_tensorAdjoint_injective N M hM hS,
    indecomposable_tensorArrow_surjective N M hM hT⟩

end
end QuantumFlags

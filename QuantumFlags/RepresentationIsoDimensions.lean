import QuantumFlags.TensorRepresentationCategory
import QuantumFlags.SimpleDimensionVectors

namespace QuantumFlags
noncomputable section
open CategoryTheory
universe u v
variable {N : DivisionBimodule.{u}}
variable {M P : TensorRepresentation.{u,max u v,max u v} N}

def tensorIsoSourceEquiv (e : M ≅ P) : M.Source ≃ₗ[N.LeftRingᵐᵒᵖ] P.Source :=
  LinearEquiv.ofLinearMap e.hom.source e.inv.source
    (congrArg TensorRepresentationMorphism.source e.inv_hom_id)
    (congrArg TensorRepresentationMorphism.source e.hom_inv_id)

def tensorIsoTargetEquiv (e : M ≅ P) : M.Target ≃ₗ[N.RightRingᵐᵒᵖ] P.Target :=
  LinearEquiv.ofLinearMap e.hom.target e.inv.target
    (congrArg TensorRepresentationMorphism.target e.inv_hom_id)
    (congrArg TensorRepresentationMorphism.target e.hom_inv_id)

theorem tensorIso_source_finrank (e : M ≅ P) :
    Module.finrank N.LeftRingᵐᵒᵖ M.Source = Module.finrank N.LeftRingᵐᵒᵖ P.Source :=
  (tensorIsoSourceEquiv e).finrank_eq

theorem tensorIso_target_finrank (e : M ≅ P) :
    Module.finrank N.RightRingᵐᵒᵖ M.Target = Module.finrank N.RightRingᵐᵒᵖ P.Target :=
  (tensorIsoTargetEquiv e).finrank_eq

theorem positiveSource_not_simpleTarget
    (hM : 0 < Module.finrank N.LeftRingᵐᵒᵖ M.Source) :
    ¬ Nonempty (M ≅ tensorSimpleTarget.{u,v} N) := by
  rintro ⟨e⟩
  have h := tensorIso_source_finrank e
  rw [simpleTarget_source_finrank] at h
  omega

theorem positiveTarget_not_simpleSource
    (hM : 0 < Module.finrank N.RightRingᵐᵒᵖ M.Target) :
    ¬ Nonempty (M ≅ tensorSimpleSource.{u,v} N) := by
  rintro ⟨e⟩
  have h := tensorIso_target_finrank e
  rw [simpleSource_target_finrank] at h
  omega

end
end QuantumFlags

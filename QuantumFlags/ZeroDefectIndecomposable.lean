import QuantumFlags.ZeroDefectClassification
import QuantumFlags.IndecomposableRepresentationArrows

namespace QuantumFlags
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
variable (N : DivisionBimodule.{u})
variable (M : TensorRepresentation.{u,max u v,max u v} N)
variable [FiniteDimensional N.LeftRingᵐᵒᵖ M.Source]
  [FiniteDimensional N.RightRingᵐᵒᵖ M.Target]

theorem equalDimension_indecomposable_source_finrank_pos
    (hM : Indecomposable M)
    (heq : Module.finrank N.LeftRingᵐᵒᵖ M.Source = Module.finrank N.RightRingᵐᵒᵖ M.Target) :
    0 < Module.finrank N.LeftRingᵐᵒᵖ M.Source := by
  by_contra h
  have hs : Module.finrank N.LeftRingᵐᵒᵖ M.Source = 0 := Nat.eq_zero_of_not_pos h
  have ht : Module.finrank N.RightRingᵐᵒᵖ M.Target = 0 := heq.symm.trans hs
  letI : Subsingleton M.Source := Module.finrank_zero_iff.mp hs
  letI : Subsingleton M.Target := Module.finrank_zero_iff.mp ht
  apply hM.1
  rw [IsZero.iff_id_eq_zero]
  apply TensorRepresentationMorphism.ext <;> apply LinearMap.ext <;> intro x <;>
    exact Subsingleton.elim _ _

variable [FiniteDimensional N.RightRingᵐᵒᵖ N.Space]

theorem nonsimple_zeroDefect_classification
    (hN : Module.finrank N.RightRingᵐᵒᵖ N.Space = 1)
    (hM : Indecomposable M)
    (hNotTarget : ¬ Nonempty (M ≅ tensorSimpleTarget.{u,v} N))
    (heq : Module.finrank N.LeftRingᵐᵒᵖ M.Source = Module.finrank N.RightRingᵐᵒᵖ M.Target) :
    Nonempty (M ≅ tensorCanonicalProjective.{u,v} N) :=
  zeroDefect_indecomposable_isCanonicalProjective N M hN heq
    (equalDimension_indecomposable_source_finrank_pos N M hM heq) hM
    (indecomposable_tensorArrow_surjective N M hM hNotTarget)

end
end QuantumFlags

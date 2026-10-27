import QuantumFlags.CanonicalProjective
import QuantumFlags.SimpleDimensionVectors

namespace QuantumFlags
noncomputable section
universe u v
variable (N : DivisionBimodule.{u})

abbrev canonicalProjectiveTensorInverse :
    ULift.{v} N.Space →ₗ[N.RightRingᵐᵒᵖ]
      BalancedTensor N (ULift.{v} N.LeftRingᵐᵒᵖ) :=
  (tensorAt N (ULift.{v} N.LeftRingᵐᵒᵖ) (ULift.up 1)).comp
    (ULift.moduleEquiv : ULift.{v} N.Space ≃ₗ[N.RightRingᵐᵒᵖ] N.Space).toLinearMap

theorem canonicalProjective_tensorInverse_right :
    (tensorCanonicalProjective.{u,v} N).arrow.comp (canonicalProjectiveTensorInverse N) =
      LinearMap.id := by
  apply LinearMap.ext; intro n
  change balancedTensorLift N _ (canonicalProjective N).arrow
    (balancedPure N _ (ULift.up 1) n.down) = n
  rw [balancedTensorLift_pure]
  change ULift.up ((1 : N.LeftRing) • n.down) = n
  simp only [one_smul, ULift.up_down]

theorem canonicalProjective_tensorInverse_left :
    (canonicalProjectiveTensorInverse.{u,v} N).comp (tensorCanonicalProjective N).arrow =
      LinearMap.id := by
  apply balancedTensor_ext
  intro x n
  change canonicalProjectiveTensorInverse N
    (balancedTensorLift N _ (canonicalProjective N).arrow (balancedPure N _ x n)) =
      balancedPure N _ x n
  rw [balancedTensorLift_pure]
  change balancedPure N _ (ULift.up 1) (x.down.unop • n) = balancedPure N _ x n
  rw [← balancedPure_balance]
  congr 1
  apply ULift.ext
  exact mul_one x.down

def canonicalProjectiveTensorEquiv :
    BalancedTensor N (ULift.{v} N.LeftRingᵐᵒᵖ) ≃ₗ[N.RightRingᵐᵒᵖ] ULift.{v} N.Space :=
  LinearEquiv.ofLinear (tensorCanonicalProjective N).arrow (canonicalProjectiveTensorInverse N)
    (canonicalProjective_tensorInverse_right N) (canonicalProjective_tensorInverse_left N)

theorem canonicalProjective_tensorArrow_bijective :
    Function.Bijective (tensorCanonicalProjective.{u,v} N).arrow :=
  (canonicalProjectiveTensorEquiv N).bijective

theorem canonicalProjective_source_finrank :
    Module.finrank N.LeftRingᵐᵒᵖ (canonicalProjective.{u,v} N).Source = 1 :=
  simpleSource_source_finrank N

theorem canonicalProjective_target_finrank :
    Module.finrank N.RightRingᵐᵒᵖ (canonicalProjective.{u,v} N).Target =
      Module.finrank N.RightRingᵐᵒᵖ N.Space :=
  (ULift.moduleEquiv : ULift.{v} N.Space ≃ₗ[N.RightRingᵐᵒᵖ] N.Space).finrank_eq

theorem canonicalProjective_dimension_vector
    (hN : Module.finrank N.RightRingᵐᵒᵖ N.Space = 1) :
    (Module.finrank N.LeftRingᵐᵒᵖ (tensorCanonicalProjective.{u,v} N).Source,
      Module.finrank N.RightRingᵐᵒᵖ (tensorCanonicalProjective.{u,v} N).Target) = (1,1) := by
  exact Prod.ext (canonicalProjective_source_finrank N)
    ((canonicalProjective_target_finrank N).trans hN)

end
end QuantumFlags

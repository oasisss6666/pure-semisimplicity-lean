import QuantumFlags.BalancedTensorDimensions
import QuantumFlags.HomFiniteDimensions
import QuantumFlags.TensorRepresentations

namespace QuantumFlags
noncomputable section
universe u
variable (N : DivisionBimodule.{u})
local instance dimensionBoundsDualModule : Module N.LeftRingᵐᵒᵖ (RightDualSpace N) := dualRightModule N
local instance dimensionBoundsHomModule (Y : Type*) [AddCommGroup Y] [Module N.RightRingᵐᵒᵖ Y] :
    Module N.LeftRingᵐᵒᵖ (BimoduleRightHom N Y) := rightHomModule N Y

variable (M : TensorRepresentation N)
  [FiniteDimensional N.LeftRingᵐᵒᵖ M.Source] [FiniteDimensional N.RightRingᵐᵒᵖ M.Target]
  [FiniteDimensional N.RightRingᵐᵒᵖ N.Space]
  [FiniteDimensional N.LeftRingᵐᵒᵖ (RightDualSpace N)]

theorem tensorRepresentation_target_finrank_le (hM : Function.Surjective M.arrow) :
    Module.finrank N.RightRingᵐᵒᵖ M.Target ≤
      Module.finrank N.LeftRingᵐᵒᵖ M.Source * Module.finrank N.RightRingᵐᵒᵖ N.Space := by
  have h := LinearMap.finrank_le_finrank_of_surjective hM
  rwa [balancedTensor_finrank] at h

theorem tensorRepresentation_source_finrank_le
    (hM : Function.Injective (tensorRepresentationToHom M).arrow) :
    Module.finrank N.LeftRingᵐᵒᵖ M.Source ≤
      Module.finrank N.LeftRingᵐᵒᵖ (RightDualSpace N) * Module.finrank N.RightRingᵐᵒᵖ M.Target := by
  have h := LinearMap.finrank_le_finrank_of_injective hM
  rw [rightHom_finrank N M.Target, Nat.mul_comm] at h
  exact h

theorem one_two_representation_dimension_bounds
    (hN : Module.finrank N.RightRingᵐᵒᵖ N.Space = 1)
    (hD : Module.finrank N.LeftRingᵐᵒᵖ (RightDualSpace N) = 2)
    (hβ : Function.Injective (tensorRepresentationToHom M).arrow)
    (hγ : Function.Surjective M.arrow) :
    Module.finrank N.RightRingᵐᵒᵖ M.Target ≤ Module.finrank N.LeftRingᵐᵒᵖ M.Source ∧
      Module.finrank N.LeftRingᵐᵒᵖ M.Source ≤ 2 * Module.finrank N.RightRingᵐᵒᵖ M.Target := by
  constructor
  · simpa only [hN, mul_one] using tensorRepresentation_target_finrank_le N M hγ
  · simpa only [hD] using tensorRepresentation_source_finrank_le N M hβ

end
end QuantumFlags

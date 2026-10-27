import QuantumFlags.TensorRepresentationDimensionBounds
import QuantumFlags.IndecomposableRepresentationArrows

namespace QuantumFlags
noncomputable section
open CategoryTheory
universe u v
variable (N : DivisionBimodule.{u})
local instance indecomposableBoundsDualModule :
    Module N.LeftRingᵐᵒᵖ (RightDualSpace N) := dualRightModule N

theorem one_two_indecomposable_dimension_bounds (M : TensorRepresentation.{u,max u v,max u v} N)
    [FiniteDimensional N.LeftRingᵐᵒᵖ M.Source] [FiniteDimensional N.RightRingᵐᵒᵖ M.Target]
    [FiniteDimensional N.RightRingᵐᵒᵖ N.Space]
    [FiniteDimensional N.LeftRingᵐᵒᵖ (RightDualSpace N)]
    (hN : Module.finrank N.RightRingᵐᵒᵖ N.Space = 1)
    (hD : Module.finrank N.LeftRingᵐᵒᵖ (RightDualSpace N) = 2)
    (hM : Indecomposable M) (hS : ¬ Nonempty (M ≅ tensorSimpleSource.{u,v} N))
    (hT : ¬ Nonempty (M ≅ tensorSimpleTarget.{u,v} N)) :
    Module.finrank N.RightRingᵐᵒᵖ M.Target ≤ Module.finrank N.LeftRingᵐᵒᵖ M.Source ∧
      Module.finrank N.LeftRingᵐᵒᵖ M.Source ≤ 2 * Module.finrank N.RightRingᵐᵒᵖ M.Target :=
  one_two_representation_dimension_bounds N M hN hD
    (indecomposable_tensorAdjoint_injective N M hM hS)
    (indecomposable_tensorArrow_surjective N M hM hT)

end
end QuantumFlags

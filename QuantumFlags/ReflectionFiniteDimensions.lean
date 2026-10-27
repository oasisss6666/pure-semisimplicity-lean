import QuantumFlags.ReflectionObjects
import QuantumFlags.BalancedTensorDimensions
import QuantumFlags.HomFiniteDimensions

namespace QuantumFlags
noncomputable section
universe u
variable (N : DivisionBimodule.{u}) [FiniteDimensional N.RightRingᵐᵒᵖ N.Space]
local instance reflectionFiniteDualModule : Module N.LeftRingᵐᵒᵖ (RightDualSpace N) := dualRightModule N
local instance reflectionFiniteHomModule (Y : Type*) [AddCommGroup Y] [Module N.RightRingᵐᵒᵖ Y] :
    Module N.LeftRingᵐᵒᵖ (BimoduleRightHom N Y) := rightHomModule N Y
local instance reflectionFiniteTensorSourceModule (L : TensorRepresentation (rightDual N)) :
    Module N.RightRingᵐᵒᵖ L.Source := L.sourceModule
local instance reflectionFiniteTensorTargetModule (L : TensorRepresentation (rightDual N)) :
    Module N.LeftRingᵐᵒᵖ L.Target := L.targetModule

variable [FiniteDimensional N.LeftRingᵐᵒᵖ (RightDualSpace N)]

instance reflectionForwardSourceFinite (M : HomRepresentation N)
    [FiniteDimensional N.RightRingᵐᵒᵖ M.Target] :
    FiniteDimensional N.RightRingᵐᵒᵖ (reflectionForward N M).Source := inferInstance

instance reflectionForwardTargetFinite (M : HomRepresentation N)
    [FiniteDimensional N.RightRingᵐᵒᵖ M.Target] :
    FiniteDimensional N.LeftRingᵐᵒᵖ (reflectionForward N M).Target := by
  change FiniteDimensional N.LeftRingᵐᵒᵖ (BimoduleRightHom N M.Target ⧸ M.arrow.range)
  infer_instance

instance reflectionBackwardSourceFinite (L : TensorRepresentation (rightDual N))
    [FiniteDimensional N.RightRingᵐᵒᵖ L.Source] :
    FiniteDimensional N.LeftRingᵐᵒᵖ (reflectionBackward N L).Source := by
  change FiniteDimensional N.LeftRingᵐᵒᵖ (LinearMap.ker L.arrow)
  letI : FiniteDimensional N.LeftRingᵐᵒᵖ (BalancedTensor (rightDual N) L.Source) :=
    balancedTensorFiniteDimensional (rightDual N) L.Source
  infer_instance

instance reflectionBackwardTargetFinite (L : TensorRepresentation (rightDual N))
    [FiniteDimensional N.RightRingᵐᵒᵖ L.Source] :
    FiniteDimensional N.RightRingᵐᵒᵖ (reflectionBackward N L).Target := inferInstance

theorem reflectionForward_finite (M : HomRepresentation N)
    [FiniteDimensional N.RightRingᵐᵒᵖ M.Target] :
    FiniteDimensional N.RightRingᵐᵒᵖ (reflectionForward N M).Source ∧
      FiniteDimensional N.LeftRingᵐᵒᵖ (reflectionForward N M).Target :=
  ⟨reflectionForwardSourceFinite N M, reflectionForwardTargetFinite N M⟩

theorem reflectionBackward_finite (L : TensorRepresentation (rightDual N))
    [FiniteDimensional N.RightRingᵐᵒᵖ L.Source] :
    FiniteDimensional N.LeftRingᵐᵒᵖ (reflectionBackward N L).Source ∧
      FiniteDimensional N.RightRingᵐᵒᵖ (reflectionBackward N L).Target :=
  ⟨reflectionBackwardSourceFinite N L, reflectionBackwardTargetFinite N L⟩

end
end QuantumFlags

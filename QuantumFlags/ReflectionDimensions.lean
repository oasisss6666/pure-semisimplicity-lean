import QuantumFlags.ReflectionObjects
import QuantumFlags.HomDimensions

namespace QuantumFlags
noncomputable section
universe u
variable (N : DivisionBimodule.{u}) [FiniteDimensional N.RightRingᵐᵒᵖ N.Space]
local instance reflectionDimensionsDualModule : Module N.LeftRingᵐᵒᵖ (RightDualSpace N) := dualRightModule N
local instance reflectionDimensionsHomModule (Y : Type*) [AddCommGroup Y] [Module N.RightRingᵐᵒᵖ Y] :
    Module N.LeftRingᵐᵒᵖ (BimoduleRightHom N Y) := rightHomModule N Y

variable (M : HomRepresentation N)
  [FiniteDimensional N.LeftRingᵐᵒᵖ M.Source] [FiniteDimensional N.RightRingᵐᵒᵖ M.Target]
  [FiniteDimensional N.LeftRingᵐᵒᵖ (RightDualSpace N)]

theorem reflectionForward_target_finrank (hM : Function.Injective M.arrow) :
    Module.finrank N.LeftRingᵐᵒᵖ (reflectionForward N M).Target =
      Module.finrank N.LeftRingᵐᵒᵖ (RightDualSpace N) * Module.finrank N.RightRingᵐᵒᵖ M.Target -
        Module.finrank N.LeftRingᵐᵒᵖ M.Source := by
  have h := reflection_cokernel_finrank N (Module.finBasis N.RightRingᵐᵒᵖ M.Target)
    (Module.finBasis N.LeftRingᵐᵒᵖ (RightDualSpace N)).equivFun M.arrow hM
  simpa only [Nat.mul_comm] using h

theorem reflectionForward_dimension_vector (hM : Function.Injective M.arrow) :
    (Module.finrank N.RightRingᵐᵒᵖ (reflectionForward N M).Source,
      Module.finrank N.LeftRingᵐᵒᵖ (reflectionForward N M).Target) =
      (Module.finrank N.RightRingᵐᵒᵖ M.Target,
        Module.finrank N.LeftRingᵐᵒᵖ (RightDualSpace N) * Module.finrank N.RightRingᵐᵒᵖ M.Target -
          Module.finrank N.LeftRingᵐᵒᵖ M.Source) :=
  Prod.ext rfl (reflectionForward_target_finrank N M hM)

end
end QuantumFlags

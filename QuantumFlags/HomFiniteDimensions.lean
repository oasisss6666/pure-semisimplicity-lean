import QuantumFlags.HomDimensions

namespace QuantumFlags
noncomputable section
universe u
variable (N : DivisionBimodule.{u})
local instance homFiniteDualModule : Module N.LeftRingᵐᵒᵖ (RightDualSpace N) := dualRightModule N
local instance homFiniteHomModule (Y : Type*) [AddCommGroup Y] [Module N.RightRingᵐᵒᵖ Y] :
    Module N.LeftRingᵐᵒᵖ (BimoduleRightHom N Y) := rightHomModule N Y

variable (Y : Type*) [AddCommGroup Y] [Module N.RightRingᵐᵒᵖ Y]
  [FiniteDimensional N.RightRingᵐᵒᵖ Y] [FiniteDimensional N.LeftRingᵐᵒᵖ (RightDualSpace N)]

instance rightHomFiniteDimensional : FiniteDimensional N.LeftRingᵐᵒᵖ (BimoduleRightHom N Y) :=
  FiniteDimensional.of_injective
    (homCoordinateEquiv N (Module.finBasis N.RightRingᵐᵒᵖ Y)
      (Module.finBasis N.LeftRingᵐᵒᵖ (RightDualSpace N)).equivFun).toLinearMap
    (homCoordinateEquiv N (Module.finBasis N.RightRingᵐᵒᵖ Y)
      (Module.finBasis N.LeftRingᵐᵒᵖ (RightDualSpace N)).equivFun).injective

theorem rightHom_finrank :
    Module.finrank N.LeftRingᵐᵒᵖ (BimoduleRightHom N Y) =
      Module.finrank N.RightRingᵐᵒᵖ Y * Module.finrank N.LeftRingᵐᵒᵖ (RightDualSpace N) :=
  hom_finrank_from_coordinates N (Module.finBasis N.RightRingᵐᵒᵖ Y)
    (Module.finBasis N.LeftRingᵐᵒᵖ (RightDualSpace N)).equivFun

end
end QuantumFlags

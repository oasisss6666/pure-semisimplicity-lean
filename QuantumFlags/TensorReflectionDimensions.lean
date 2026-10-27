import QuantumFlags.TensorReflectionEquivalence
import QuantumFlags.ReflectionDimensions

namespace QuantumFlags
noncomputable section
universe u v
variable (N : DivisionBimodule.{u}) [FiniteDimensional N.RightRingᵐᵒᵖ N.Space]
local instance tensorReflectionDimensionsDualModule :
    Module N.LeftRingᵐᵒᵖ (RightDualSpace N) := dualRightModule N

variable (M : InjectiveTensorObjects.{u,v} N)
  [FiniteDimensional N.LeftRingᵐᵒᵖ M.val.Source]
  [FiniteDimensional N.RightRingᵐᵒᵖ M.val.Target]
  [FiniteDimensional N.LeftRingᵐᵒᵖ (RightDualSpace N)]

theorem tensorReflection_dimension_vector :
    (Module.finrank N.RightRingᵐᵒᵖ
        (reflectionForward N (tensorRepresentationToHom M.val)).Source,
      Module.finrank N.LeftRingᵐᵒᵖ
        (reflectionForward N (tensorRepresentationToHom M.val)).Target) =
      (Module.finrank N.RightRingᵐᵒᵖ M.val.Target,
        Module.finrank N.LeftRingᵐᵒᵖ (RightDualSpace N) *
          Module.finrank N.RightRingᵐᵒᵖ M.val.Target -
            Module.finrank N.LeftRingᵐᵒᵖ M.val.Source) :=
  reflectionForward_dimension_vector N (tensorRepresentationToHom M.val) M.property

end
end QuantumFlags

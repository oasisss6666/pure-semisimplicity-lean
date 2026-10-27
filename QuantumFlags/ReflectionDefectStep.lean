import QuantumFlags.TensorReflectionDimensions
import QuantumFlags.TensorRepresentationDimensionBounds
import QuantumFlags.ReflectionFiniteDimensions

namespace QuantumFlags
noncomputable section
universe u v
variable (N : DivisionBimodule.{u}) [FiniteDimensional N.RightRingᵐᵒᵖ N.Space]
local instance defectStepDualModule : Module N.LeftRingᵐᵒᵖ (RightDualSpace N) := dualRightModule N

theorem tensorReflection_positive_defect_step (M : InjectiveTensorObjects.{u,v} N)
    [FiniteDimensional N.LeftRingᵐᵒᵖ M.val.Source]
    [FiniteDimensional N.RightRingᵐᵒᵖ M.val.Target]
    [FiniteDimensional N.LeftRingᵐᵒᵖ (RightDualSpace N)]
    (hD : Module.finrank N.LeftRingᵐᵒᵖ (RightDualSpace N) = 2)
    (hdef : Module.finrank N.RightRingᵐᵒᵖ M.val.Target <
      Module.finrank N.LeftRingᵐᵒᵖ M.val.Source) :
    Module.finrank N.LeftRingᵐᵒᵖ
        (reflectionForward N (tensorRepresentationToHom M.val)).Target <
      Module.finrank N.RightRingᵐᵒᵖ M.val.Target ∧
    Module.finrank N.RightRingᵐᵒᵖ
        (reflectionForward N (tensorRepresentationToHom M.val)).Source -
      Module.finrank N.LeftRingᵐᵒᵖ
        (reflectionForward N (tensorRepresentationToHom M.val)).Target =
      Module.finrank N.LeftRingᵐᵒᵖ M.val.Source - Module.finrank N.RightRingᵐᵒᵖ M.val.Target := by
  have hu := tensorRepresentation_source_finrank_le N M.val M.property
  rw [hD] at hu
  have hd := reflectionForward_target_finrank N (tensorRepresentationToHom M.val) M.property
  rw [hD] at hd
  change Module.finrank N.LeftRingᵐᵒᵖ
      (reflectionForward N (tensorRepresentationToHom M.val)).Target =
    2 * Module.finrank N.RightRingᵐᵒᵖ M.val.Target -
      Module.finrank N.LeftRingᵐᵒᵖ M.val.Source at hd
  constructor
  · rw [hd]
    omega
  · change Module.finrank N.RightRingᵐᵒᵖ M.val.Target -
        Module.finrank N.LeftRingᵐᵒᵖ (reflectionForward N (tensorRepresentationToHom M.val)).Target = _
    rw [hd]
    omega

end
end QuantumFlags

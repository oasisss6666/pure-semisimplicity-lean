import QuantumFlags.ReflectionFiniteDimensions
import QuantumFlags.TensorReflectionEquivalence

namespace QuantumFlags
noncomputable section
universe u v
variable (N : DivisionBimodule.{u}) [FiniteDimensional N.RightRingᵐᵒᵖ N.Space]
local instance inverseDimensionsDualModule : Module N.LeftRingᵐᵒᵖ (RightDualSpace N) := dualRightModule N
local instance inverseDimensionsSourceModule (L : TensorRepresentation (rightDual N)) :
    Module N.RightRingᵐᵒᵖ L.Source := L.sourceModule
local instance inverseDimensionsTargetModule (L : TensorRepresentation (rightDual N)) :
    Module N.LeftRingᵐᵒᵖ L.Target := L.targetModule
variable [FiniteDimensional N.LeftRingᵐᵒᵖ (RightDualSpace N)]

theorem reflectionBackward_source_finrank (L : TensorRepresentation (rightDual N))
    [FiniteDimensional N.RightRingᵐᵒᵖ L.Source] [FiniteDimensional N.LeftRingᵐᵒᵖ L.Target]
    (hL : Function.Surjective L.arrow) :
    Module.finrank N.LeftRingᵐᵒᵖ (reflectionBackward N L).Source =
      Module.finrank N.LeftRingᵐᵒᵖ (RightDualSpace N) * Module.finrank N.RightRingᵐᵒᵖ L.Source -
        Module.finrank N.LeftRingᵐᵒᵖ L.Target := by
  letI : FiniteDimensional N.LeftRingᵐᵒᵖ (BalancedTensor (rightDual N) L.Source) :=
    balancedTensorFiniteDimensional (rightDual N) L.Source
  have h := L.arrow.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hL, finrank_top, balancedTensor_finrank, Nat.mul_comm] at h
  change Module.finrank N.LeftRingᵐᵒᵖ L.Target +
      Module.finrank N.LeftRingᵐᵒᵖ (reflectionBackward N L).Source =
    Module.finrank N.LeftRingᵐᵒᵖ (RightDualSpace N) * Module.finrank N.RightRingᵐᵒᵖ L.Source at h
  omega

theorem reflectionBackward_dimension_vector (L : TensorRepresentation (rightDual N))
    [FiniteDimensional N.RightRingᵐᵒᵖ L.Source] [FiniteDimensional N.LeftRingᵐᵒᵖ L.Target]
    (hL : Function.Surjective L.arrow) :
    (Module.finrank N.LeftRingᵐᵒᵖ (reflectionBackward N L).Source,
      Module.finrank N.RightRingᵐᵒᵖ (reflectionBackward N L).Target) =
      (Module.finrank N.LeftRingᵐᵒᵖ (RightDualSpace N) * Module.finrank N.RightRingᵐᵒᵖ L.Source -
        Module.finrank N.LeftRingᵐᵒᵖ L.Target,
        Module.finrank N.RightRingᵐᵒᵖ L.Source) :=
  Prod.ext (reflectionBackward_source_finrank N L hL) rfl

theorem inverseTensorReflection_dimension_vector (L : SurjectiveDualTensorObjects.{u,v} N)
    [FiniteDimensional N.RightRingᵐᵒᵖ L.val.Source] [FiniteDimensional N.LeftRingᵐᵒᵖ L.val.Target] :
    (Module.finrank N.LeftRingᵐᵒᵖ (homRepresentationToTensor (reflectionBackward N L.val)).Source,
      Module.finrank N.RightRingᵐᵒᵖ (homRepresentationToTensor (reflectionBackward N L.val)).Target) =
      (Module.finrank N.LeftRingᵐᵒᵖ (RightDualSpace N) * Module.finrank N.RightRingᵐᵒᵖ L.val.Source -
        Module.finrank N.LeftRingᵐᵒᵖ L.val.Target,
        Module.finrank N.RightRingᵐᵒᵖ L.val.Source) :=
  reflectionBackward_dimension_vector N L.val L.property

end
end QuantumFlags

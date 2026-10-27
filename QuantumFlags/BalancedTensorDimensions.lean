import QuantumFlags.BalancedTensorCoordinates

namespace QuantumFlags
noncomputable section
universe u
variable (N : DivisionBimodule.{u}) (X : Type*) [AddCommGroup X] [Module N.LeftRingᵐᵒᵖ X]
  [FiniteDimensional N.LeftRingᵐᵒᵖ X] [FiniteDimensional N.RightRingᵐᵒᵖ N.Space]

instance balancedTensorFiniteDimensional : FiniteDimensional N.RightRingᵐᵒᵖ (BalancedTensor N X) :=
  FiniteDimensional.of_injective
    (balancedTensorBasisEquiv N X (Module.finBasis N.LeftRingᵐᵒᵖ X)).toLinearMap
    (balancedTensorBasisEquiv N X (Module.finBasis N.LeftRingᵐᵒᵖ X)).injective

theorem balancedTensor_finrank :
    Module.finrank N.RightRingᵐᵒᵖ (BalancedTensor N X) =
      Module.finrank N.LeftRingᵐᵒᵖ X * Module.finrank N.RightRingᵐᵒᵖ N.Space := by
  rw [(balancedTensorBasisEquiv N X (Module.finBasis N.LeftRingᵐᵒᵖ X)).finrank_eq,
    Module.finrank_pi_fintype]
  simp

end
end QuantumFlags

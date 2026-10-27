import QuantumFlags.TensorSimpleSummands

namespace QuantumFlags
noncomputable section
universe u v
variable (N : DivisionBimodule.{u})

theorem simpleSource_source_finrank :
    Module.finrank N.LeftRingᵐᵒᵖ (simpleSource.{u,v} N).Source = 1 := by
  simpa only [Module.finrank_self] using
    (ULift.moduleEquiv : ULift.{v} N.LeftRingᵐᵒᵖ ≃ₗ[N.LeftRingᵐᵒᵖ] N.LeftRingᵐᵒᵖ).finrank_eq

theorem simpleSource_target_finrank :
    Module.finrank N.RightRingᵐᵒᵖ (simpleSource.{u,v} N).Target = 0 :=
  Module.finrank_eq_zero_of_subsingleton (R := N.RightRingᵐᵒᵖ) (M := PUnit.{max u v + 1})

theorem simpleTarget_source_finrank :
    Module.finrank N.LeftRingᵐᵒᵖ (simpleTarget.{u,v} N).Source = 0 :=
  Module.finrank_eq_zero_of_subsingleton (R := N.LeftRingᵐᵒᵖ) (M := PUnit.{max u v + 1})

theorem simpleTarget_target_finrank :
    Module.finrank N.RightRingᵐᵒᵖ (simpleTarget.{u,v} N).Target = 1 := by
  simpa only [Module.finrank_self] using
    (ULift.moduleEquiv : ULift.{v} N.RightRingᵐᵒᵖ ≃ₗ[N.RightRingᵐᵒᵖ] N.RightRingᵐᵒᵖ).finrank_eq

theorem tensorSimpleSource_dimension_vector :
    (Module.finrank N.LeftRingᵐᵒᵖ (tensorSimpleSource.{u,v} N).Source,
      Module.finrank N.RightRingᵐᵒᵖ (tensorSimpleSource.{u,v} N).Target) = (1,0) :=
  Prod.ext (simpleSource_source_finrank N) (simpleSource_target_finrank N)

theorem tensorSimpleTarget_dimension_vector :
    (Module.finrank N.LeftRingᵐᵒᵖ (tensorSimpleTarget.{u,v} N).Source,
      Module.finrank N.RightRingᵐᵒᵖ (tensorSimpleTarget.{u,v} N).Target) = (0,1) :=
  Prod.ext (simpleTarget_source_finrank N) (simpleTarget_target_finrank N)

end
end QuantumFlags

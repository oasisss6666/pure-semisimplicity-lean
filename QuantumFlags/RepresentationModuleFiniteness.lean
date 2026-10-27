import QuantumFlags.BimoduleRepresentationApplications
import QuantumFlags.BimoduleArtinian

namespace QuantumFlags
noncomputable section
universe u v
variable (N : DivisionBimodule.{u}) [FiniteDimensional N.RightRingᵐᵒᵖ N.Space]

theorem bimoduleTensorRepresentation_finite
    (M : TensorRepresentation.{u,max u v,max u v} N)
    [FiniteDimensional N.LeftRingᵐᵒᵖ M.Source]
    [FiniteDimensional N.RightRingᵐᵒᵖ M.Target] :
    Module.Finite (BimoduleTriangularRing N)ᵐᵒᵖ
      ((bimoduleTensorRepresentationEquivalence N).functor.obj M) := by
  letI := bimoduleModuleFromHomRepresentation N (tensorRepresentationToHom M)
  apply (bimodule_finite_iff_corners N (M.Source × M.Target)).mpr
  constructor
  · exact FiniteDimensional.of_injective
      (bimoduleSourceRecoveryEquiv N (tensorRepresentationToHom M)).toLinearMap
      (bimoduleSourceRecoveryEquiv N (tensorRepresentationToHom M)).injective
  · exact FiniteDimensional.of_injective
      (bimoduleTargetRecoveryEquiv N (tensorRepresentationToHom M)).toLinearMap
      (bimoduleTargetRecoveryEquiv N (tensorRepresentationToHom M)).injective

end
end QuantumFlags

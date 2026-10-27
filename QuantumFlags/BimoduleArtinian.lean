import QuantumFlags.BimoduleRegularCorners
import QuantumFlags.TwoCornerSubmodules

namespace QuantumFlags

noncomputable section

universe u

variable (N : DivisionBimodule.{u}) [FiniteDimensional N.RightRingᵐᵒᵖ N.Space]

theorem bimodule_triangular_op_artinian : IsArtinianRing (BimoduleTriangularRing N)ᵐᵒᵖ := by
  letI := cornerFixedModule (bimoduleSourceCornerHom N) (BimoduleTriangularRing N)ᵐᵒᵖ
  letI := cornerFixedModule (bimoduleTargetCornerHom N) (BimoduleTriangularRing N)ᵐᵒᵖ
  letI := bimodule_source_regular_finite N
  letI := bimodule_target_regular_finite N
  exact artinian_of_two_corners (bimoduleSourceCornerHom N) (bimoduleTargetCornerHom N)
    (bimodule_corner_units_sum N) (BimoduleTriangularRing N)ᵐᵒᵖ inferInstance inferInstance

theorem bimodule_triangular_right_artinian :
    IsArtinian (BimoduleTriangularRing N)ᵐᵒᵖ (BimoduleTriangularRing N) := by
  letI := bimodule_triangular_op_artinian N
  let e : (BimoduleTriangularRing N)ᵐᵒᵖ ≃ₗ[(BimoduleTriangularRing N)ᵐᵒᵖ] BimoduleTriangularRing N := {
    toFun := MulOpposite.unop
    invFun := MulOpposite.op
    left_inv := MulOpposite.op_unop
    right_inv := MulOpposite.unop_op
    map_add' := MulOpposite.unop_add
    map_smul' _ _ := rfl }
  exact isArtinian_of_linearEquiv e

theorem bimodule_triangular_op_noetherian : IsNoetherianRing (BimoduleTriangularRing N)ᵐᵒᵖ := by
  letI := cornerFixedModule (bimoduleSourceCornerHom N) (BimoduleTriangularRing N)ᵐᵒᵖ
  letI := cornerFixedModule (bimoduleTargetCornerHom N) (BimoduleTriangularRing N)ᵐᵒᵖ
  letI := bimodule_source_regular_finite N
  letI := bimodule_target_regular_finite N
  exact noetherian_of_two_corners (bimoduleSourceCornerHom N) (bimoduleTargetCornerHom N)
    (bimodule_corner_units_sum N) (BimoduleTriangularRing N)ᵐᵒᵖ inferInstance inferInstance

theorem bimodule_finite_iff_corners (M : Type*) [AddCommGroup M]
    [Module (BimoduleTriangularRing N)ᵐᵒᵖ M] :
    letI := cornerFixedModule (bimoduleSourceCornerHom N) M
    letI := cornerFixedModule (bimoduleTargetCornerHom N) M
    Module.Finite (BimoduleTriangularRing N)ᵐᵒᵖ M ↔
      FiniteDimensional N.LeftRingᵐᵒᵖ (cornerFixedGroup (bimoduleSourceCornerHom N) M) ∧
      FiniteDimensional N.RightRingᵐᵒᵖ (cornerFixedGroup (bimoduleTargetCornerHom N) M) := by
  letI := cornerFixedModule (bimoduleSourceCornerHom N) M
  letI := cornerFixedModule (bimoduleTargetCornerHom N) M
  constructor
  · intro h
    letI := h
    exact ⟨corner_finite_of_finite (bimoduleSourceCornerHom N) M (bimodule_source_regular_finite N),
      corner_finite_of_finite (bimoduleTargetCornerHom N) M (bimodule_target_regular_finite N)⟩
  · rintro ⟨hs,ht⟩
    letI := hs
    letI := ht
    letI : IsNoetherian (BimoduleTriangularRing N)ᵐᵒᵖ M :=
      noetherian_of_two_corners (bimoduleSourceCornerHom N) (bimoduleTargetCornerHom N)
        (bimodule_corner_units_sum N) M inferInstance inferInstance
    infer_instance

theorem bimodule_finite_presentation (M : Type*) [AddCommGroup M]
    [Module (BimoduleTriangularRing N)ᵐᵒᵖ M] [Module.Finite (BimoduleTriangularRing N)ᵐᵒᵖ M] :
    Module.FinitePresentation (BimoduleTriangularRing N)ᵐᵒᵖ M := by
  letI := bimodule_triangular_op_noetherian N
  exact Module.finitePresentation_of_finite (BimoduleTriangularRing N)ᵐᵒᵖ M

end

end QuantumFlags

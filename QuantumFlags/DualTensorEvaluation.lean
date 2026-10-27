import QuantumFlags.BalancedTensor

namespace QuantumFlags
noncomputable section
universe u v
variable (N : DivisionBimodule.{u}) (Y : Type v) [AddCommGroup Y]
  [Module N.RightRingᵐᵒᵖ Y]

local instance : Module N.LeftRingᵐᵒᵖ (RightDualSpace N) := dualRightModule N
local instance : Module N.LeftRingᵐᵒᵖ (BimoduleRightHom N Y) := rightHomModule N Y

def dualEvaluationValue (y : Y) (φ : RightDualSpace N) : BimoduleRightHom N Y where
  toFun n := MulOpposite.op (φ n) • y
  map_add' m n := by simp [map_add, add_smul]
  map_smul' b n := by
    change MulOpposite.op (φ (b • n)) • y = b • (MulOpposite.op (φ n) • y)
    rw [φ.map_smul]
    change MulOpposite.op (φ n * b.unop) • y = b • (MulOpposite.op (φ n) • y)
    rw [← mul_smul]
    rfl

def dualEvaluationAt (y : Y) :
    letI := rightHomModule N Y
    BimoduleRightHom (rightDual N) (BimoduleRightHom N Y) := by
  letI := rightHomModule N Y
  exact {
    toFun := dualEvaluationValue N Y y
    map_add' φ ψ := by
      apply LinearMap.ext
      intro n
      change MulOpposite.op (φ n + ψ n) • y = _
      exact add_smul _ _ _
    map_smul' a φ := by
      apply LinearMap.ext
      intro n
      rfl }

def dualEvaluationAdjoint :
    letI := rightHomModule N Y
    letI := rightHomModule (rightDual N) (BimoduleRightHom N Y)
    Y →ₗ[N.RightRingᵐᵒᵖ] BimoduleRightHom (rightDual N) (BimoduleRightHom N Y) := by
  letI := rightHomModule N Y
  letI := rightHomModule (rightDual N) (BimoduleRightHom N Y)
  exact {
    toFun := dualEvaluationAt N Y
    map_add' y z := by
      apply LinearMap.ext
      intro φ
      apply LinearMap.ext
      intro n
      exact smul_add _ _ _
    map_smul' b y := by
      apply LinearMap.ext
      intro φ
      apply LinearMap.ext
      intro n
      change MulOpposite.op (φ n) • (b • y) = MulOpposite.op (b.unop * φ n) • y
      rw [← mul_smul]
      rfl }

def dualTensorEvaluation :
    letI := rightHomModule N Y
    BalancedTensor (rightDual N) Y →ₗ[N.LeftRingᵐᵒᵖ] BimoduleRightHom N Y := by
  letI := rightHomModule N Y
  exact balancedTensorLift (rightDual N) Y (dualEvaluationAdjoint N Y)

theorem dualTensorEvaluation_pure (y : Y) (φ : RightDualSpace N) (n : N.Space) :
    dualTensorEvaluation N Y (balancedPure (rightDual N) Y y φ) n =
      MulOpposite.op (φ n) • y := by
  have h := balancedTensorLift_pure (rightDual N) Y (dualEvaluationAdjoint N Y) y φ
  exact congrArg (fun f : BimoduleRightHom N Y => f n) h

end
end QuantumFlags

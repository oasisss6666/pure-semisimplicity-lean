import QuantumFlags.DualTensorEvaluation

namespace QuantumFlags
noncomputable section
universe u v
variable (N : DivisionBimodule.{u})
local instance : Module N.LeftRingᵐᵒᵖ (RightDualSpace N) := dualRightModule N
variable {ι : Type*} [Fintype ι] (b : Module.Basis ι N.RightRingᵐᵒᵖ N.Space)

def rightDualCoordinate (i : ι) : RightDualSpace N where
  toFun n := (b.repr n i).unop
  map_add' m n := by simp [map_add]
  map_smul' a n := by
    change (b.repr (a • n) i).unop = _
    rw [map_smul]
    rfl

theorem rightDualCoordinate_expansion (φ : RightDualSpace N) :
    (∑ i, φ (b i) • rightDualCoordinate N b i) = φ := by
  apply LinearMap.ext
  intro n
  have h := congrArg φ (b.sum_repr n)
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  change (∑ i, φ (b i) * (b.repr n i).unop) = φ n
  simpa only [map_sum, map_smul, MulOpposite.smul_eq_mul_unop] using h

variable (Y : Type v) [AddCommGroup Y] [Module N.RightRingᵐᵒᵖ Y]

def dualTensorInverseAdd : BimoduleRightHom N Y →+ BalancedTensor (rightDual N) Y where
  toFun f := ∑ i, balancedPure (rightDual N) Y (f (b i)) (rightDualCoordinate N b i)
  map_zero' := by simp [balancedPure_zero_left]
  map_add' f g := by
    simp only [LinearMap.add_apply, balancedPure_add_left, Finset.sum_add_distrib]

theorem dualTensorEvaluation_inverse (f : BimoduleRightHom N Y) :
    dualTensorEvaluation N Y (dualTensorInverseAdd N b Y f) = f := by
  apply LinearMap.ext
  intro n
  have h := congrArg f (b.sum_repr n)
  change dualTensorEvaluation N Y (∑ i, balancedPure (rightDual N) Y
    (f (b i)) (rightDualCoordinate N b i)) n = f n
  rw [map_sum]
  simp only [LinearMap.sum_apply, dualTensorEvaluation_pure]
  change (∑ i, b.repr n i • f (b i)) = f n
  simpa only [map_sum, map_smul] using h

theorem dualTensorInverse_pure (y : Y) (φ : RightDualSpace N) :
    dualTensorInverseAdd N b Y
      (dualTensorEvaluation N Y (balancedPure (rightDual N) Y y φ)) =
      balancedPure (rightDual N) Y y φ := by
  change (∑ i, balancedPure (rightDual N) Y
    (dualTensorEvaluation N Y (balancedPure (rightDual N) Y y φ) (b i))
      (rightDualCoordinate N b i)) = _
  simp only [dualTensorEvaluation_pure]
  have hb (i : ι) := balancedPure_balance (rightDual N) Y (φ (b i)) y (rightDualCoordinate N b i)
  simp_rw [hb]
  change (∑ i, tensorAt (rightDual N) Y y (φ (b i) • rightDualCoordinate N b i)) = _
  rw [← map_sum, rightDualCoordinate_expansion]
  rfl

theorem balancedTensor_addHom_ext (M : DivisionBimodule.{u}) (X : Type*) [AddCommGroup X]
    [Module M.LeftRingᵐᵒᵖ X] {Z : Type*} [AddCommGroup Z]
    {f g : BalancedTensor M X →+ Z}
    (h : ∀ x n, f (balancedPure M X x n) = g (balancedPure M X x n)) : f = g := by
  have he : f.comp (balancedRelations M X).mkQ.toAddMonoidHom =
      g.comp (balancedRelations M X).mkQ.toAddMonoidHom := by
    apply Finsupp.addHom_ext
    exact h
  apply AddMonoidHom.ext
  intro z
  obtain ⟨z,rfl⟩ := (balancedRelations M X).mkQ_surjective z
  exact DFunLike.congr_fun he z

theorem dualTensorInverse_evaluation (z : BalancedTensor (rightDual N) Y) :
    dualTensorInverseAdd N b Y (dualTensorEvaluation N Y z) = z := by
  letI := rightHomModule N Y
  have h : (dualTensorInverseAdd N b Y).comp (dualTensorEvaluation N Y).toAddMonoidHom =
      AddMonoidHom.id _ := by
    apply balancedTensor_addHom_ext
    intro y φ
    exact dualTensorInverse_pure N b Y y φ
  exact DFunLike.congr_fun h z

def finiteDualTensorHomEquiv :
    letI := rightHomModule N Y
    BalancedTensor (rightDual N) Y ≃ₗ[N.LeftRingᵐᵒᵖ] BimoduleRightHom N Y := by
  letI := rightHomModule N Y
  apply LinearEquiv.ofBijective (dualTensorEvaluation N Y)
  constructor
  · intro z z' h
    have he := congrArg (dualTensorInverseAdd N b Y) h
    simpa only [dualTensorInverse_evaluation] using he
  · intro f
    exact ⟨dualTensorInverseAdd N b Y f, dualTensorEvaluation_inverse N b Y f⟩


def dualTensorHomEquiv [FiniteDimensional N.RightRingᵐᵒᵖ N.Space] :
    letI := rightHomModule N Y
    BalancedTensor (rightDual N) Y ≃ₗ[N.LeftRingᵐᵒᵖ] BimoduleRightHom N Y :=
  finiteDualTensorHomEquiv N (Module.finBasis N.RightRingᵐᵒᵖ N.Space) Y

theorem dualTensorHomEquiv_pure [FiniteDimensional N.RightRingᵐᵒᵖ N.Space]
    (y : Y) (φ : RightDualSpace N) (n : N.Space) :
    dualTensorHomEquiv N Y (balancedPure (rightDual N) Y y φ) n =
      MulOpposite.op (φ n) • y :=
  dualTensorEvaluation_pure N Y y φ n

theorem dualTensorEvaluation_natural {Z : Type*} [AddCommGroup Z]
    [Module N.RightRingᵐᵒᵖ Z] (f : Y →ₗ[N.RightRingᵐᵒᵖ] Z) :
    letI := rightHomModule N Y
    letI := rightHomModule N Z
    (rightHomMap N f).comp (dualTensorEvaluation N Y) =
      (dualTensorEvaluation N Z).comp (balancedTensorMap (rightDual N) Y f) := by
  letI := rightHomModule N Y
  letI := rightHomModule N Z
  apply balancedTensor_ext (rightDual N) Y
  intro y φ
  apply LinearMap.ext
  intro n
  change f (dualTensorEvaluation N Y (balancedPure (rightDual N) Y y φ) n) =
    dualTensorEvaluation N Z
      (balancedTensorMap (rightDual N) Y f (balancedPure (rightDual N) Y y φ)) n
  rw [balancedTensorMap_pure, dualTensorEvaluation_pure, dualTensorEvaluation_pure]
  exact f.map_smul _ _

theorem dualTensorHomEquiv_natural [FiniteDimensional N.RightRingᵐᵒᵖ N.Space]
    {Z : Type*} [AddCommGroup Z] [Module N.RightRingᵐᵒᵖ Z]
    (f : Y →ₗ[N.RightRingᵐᵒᵖ] Z) :
    letI := rightHomModule N Y
    letI := rightHomModule N Z
    (rightHomMap N f).comp (dualTensorHomEquiv N Y).toLinearMap =
      (dualTensorHomEquiv N Z).toLinearMap.comp (balancedTensorMap (rightDual N) Y f) :=
  dualTensorEvaluation_natural N Y f

end
end QuantumFlags

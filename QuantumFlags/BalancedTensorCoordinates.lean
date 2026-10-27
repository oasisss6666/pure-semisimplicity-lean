import QuantumFlags.BalancedTensor

namespace QuantumFlags
noncomputable section
universe u
variable (N : DivisionBimodule.{u}) (X : Type*) [AddCommGroup X] [Module N.LeftRingᵐᵒᵖ X]

def balancedPureLeftAddHom (n : N.Space) : X →+ BalancedTensor N X where
  toFun x := balancedPure N X x n
  map_zero' := balancedPure_zero_left N X n
  map_add' x y := balancedPure_add_left N X x y n

variable {I : Type*} [Fintype I] (b : Module.Basis I N.LeftRingᵐᵒᵖ X)

def balancedTensorCoordinateArrow :
    letI := rightHomModule N (I → N.Space)
    X →ₗ[N.LeftRingᵐᵒᵖ] BimoduleRightHom N (I → N.Space) := by
  letI := rightHomModule N (I → N.Space)
  exact {
    toFun x := {
      toFun n i := (b.repr x i).unop • n
      map_add' n m := by funext i; exact smul_add _ n m
      map_smul' r n := by funext i; exact smul_comm _ r n }
    map_add' x y := by
      apply LinearMap.ext
      intro n
      funext i
      change (b.repr (x+y) i).unop • n = (b.repr x i).unop • n + (b.repr y i).unop • n
      rw [map_add, Finsupp.add_apply, MulOpposite.unop_add, add_smul]
    map_smul' a x := by
      apply LinearMap.ext
      intro n
      funext i
      change (b.repr (a • x) i).unop • n = (b.repr x i).unop • (a.unop • n)
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, MulOpposite.unop_mul, mul_smul] }

def balancedTensorCoordinates : BalancedTensor N X →ₗ[N.RightRingᵐᵒᵖ] (I → N.Space) :=
  balancedTensorLift N X (balancedTensorCoordinateArrow N X b)

theorem balancedTensorCoordinates_pure (x : X) (n : N.Space) (i : I) :
    balancedTensorCoordinates N X b (balancedPure N X x n) i = (b.repr x i).unop • n := by
  rw [balancedTensorCoordinates, balancedTensorLift_pure]
  rfl

def balancedTensorBasisInverse : (I → N.Space) →ₗ[N.RightRingᵐᵒᵖ] BalancedTensor N X :=
  ∑ i, (tensorAt N X (b i)).comp (LinearMap.proj i)

theorem balancedTensorBasisInverse_coordinates_pure (x : X) (n : N.Space) :
    balancedTensorBasisInverse N X b
      (balancedTensorCoordinates N X b (balancedPure N X x n)) = balancedPure N X x n := by
  classical
  simp only [balancedTensorBasisInverse, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, balancedTensorCoordinates_pure]
  change (∑ i, balancedPure N X (b i) ((b.repr x i).unop • n)) = balancedPure N X x n
  calc
    _ = ∑ i, balancedPure N X ((b.repr x i) • b i) n := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [MulOpposite.op_unop] using
        (balancedPure_balance N X (b.repr x i).unop (b i) n).symm
    _ = balancedPure N X (∑ i, (b.repr x i) • b i) n :=
      (map_sum (balancedPureLeftAddHom N X n) _ Finset.univ).symm
    _ = balancedPure N X x n := by rw [b.sum_repr x]

theorem balancedTensorBasisInverse_coordinates (z : BalancedTensor N X) :
    balancedTensorBasisInverse N X b (balancedTensorCoordinates N X b z) = z := by
  have h : (balancedTensorBasisInverse N X b).comp (balancedTensorCoordinates N X b) =
      LinearMap.id := by
    apply balancedTensor_ext N X
    intro x n
    exact balancedTensorBasisInverse_coordinates_pure N X b x n
  exact LinearMap.congr_fun h z

theorem balancedTensorCoordinates_basisInverse (y : I → N.Space) :
    balancedTensorCoordinates N X b (balancedTensorBasisInverse N X b y) = y := by
  classical
  funext j
  simp only [balancedTensorBasisInverse, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, map_sum, Finset.sum_apply]
  change (∑ i, balancedTensorCoordinates N X b (balancedPure N X (b i) (y i)) j) = y j
  simp only [balancedTensorCoordinates_pure]
  rw [Finset.sum_eq_single j]
  · simp [b.repr_self]
  · intro i _ hij
    have hc : b.repr (b i) j = 0 := by
      rw [b.repr_self]
      exact Finsupp.single_eq_of_ne (Ne.symm hij)
    rw [hc, MulOpposite.unop_zero, zero_smul]
  · intro h
    exact False.elim (h (Finset.mem_univ j))

def balancedTensorBasisEquiv : BalancedTensor N X ≃ₗ[N.RightRingᵐᵒᵖ] (I → N.Space) where
  toLinearMap := balancedTensorCoordinates N X b
  invFun := balancedTensorBasisInverse N X b
  left_inv := balancedTensorBasisInverse_coordinates N X b
  right_inv := balancedTensorCoordinates_basisInverse N X b

end
end QuantumFlags

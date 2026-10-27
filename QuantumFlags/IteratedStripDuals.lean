import QuantumFlags.DualTwist
import QuantumFlags.BimoduleEquivalence

namespace QuantumFlags

noncomputable section

universe u

variable {D : Type u} [DivisionRing D]

abbrev stripBimodule (S : FlagSystem D) (k : ℕ) : DivisionBimodule.{u} where
  LeftRing := S.H k
  RightRing := S.H (k+1)
  Space := StripSpace S k

def stripDualModelEquivalence (S : FlagSystem D) (k : ℕ) :
    BimoduleEquivalence (rightDual (stripBimodule S k)) (stripBimodule S (k+1)) where
  left := RingEquiv.refl _
  right := reciprocalEquiv S k
  space := (stripDualEquiv S k).symm.toAddEquiv
  map_left a φ := (stripDualEquiv S k).symm.map_smul a φ
  map_right a φ := by
    apply (stripDualEquiv S k).injective
    change stripDualEquiv S k ((stripDualEquiv S k).symm
      (φ.comp (stripLeftMultiplication S k a))) =
      stripDualEquiv S k (MulOpposite.op (reciprocalEquiv S k a) •
        (stripDualEquiv S k).symm φ)
    rw [LinearEquiv.apply_symm_apply, ← stripDualEquiv_twist,
      LinearEquiv.apply_symm_apply]

def ambientDualEvaluation (H : Subfield D) :
    (rightDual (ambientBimodule H)).Space ≃+ D where
  toFun φ := φ 1
  invFun a := {
    toFun x := a*x
    map_add' x y := mul_add a x y
    map_smul' r x := by
      change a*(x*r.unop) = (a*x)*r.unop
      exact (mul_assoc a x r.unop).symm }
  left_inv φ := by
    apply LinearMap.ext
    intro x
    have h := φ.map_smul (MulOpposite.op x) 1
    change φ (1*x) = φ 1*x at h
    simpa using h.symm
  right_inv a := mul_one a
  map_add' φ ψ := rfl

theorem ambientDualEvaluation_apply (H : Subfield D)
    (φ : (rightDual (ambientBimodule H)).Space) : ambientDualEvaluation H φ = φ 1 := rfl

def zeroFieldEquiv (S : FlagSystem D) : D ≃+* S.H 0 where
  toFun x := ⟨x, by rw [S.zero]; trivial⟩
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

def zeroStripEquiv (S : FlagSystem D) : D ≃+ StripSpace S 0 where
  toFun x := ⟨x, by change x ∈ strip S 0; rw [strip_zero]; trivial⟩
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

def firstDualStripEquivalence (S : FlagSystem D) :
    BimoduleEquivalence (rightDual (ambientBimodule (S.H 1))) (stripBimodule S 0) where
  left := zeroFieldEquiv S
  right := RingEquiv.refl _
  space := (ambientDualEvaluation (S.H 1)).trans (zeroStripEquiv S)
  map_left a φ := by
    apply Subtype.ext
    rfl
  map_right a φ := by
    apply Subtype.ext
    change φ ((a : D)*1) = φ 1*(a : D)
    have h := φ.map_smul (MulOpposite.op (a : D)) 1
    change φ (1*(a : D)) = φ 1*(a : D) at h
    simpa using h

def iteratedDualStripEquivalence (S : FlagSystem D) : (k : ℕ) →
    BimoduleEquivalence (iteratedRightDual (ambientBimodule (S.H 1)) (k+1)) (stripBimodule S k)
  | 0 => firstDualStripEquivalence S
  | k+1 => (iteratedDualStripEquivalence S k).dual.trans (stripDualModelEquivalence S k)

theorem strip_right_rank (S : FlagSystem D) (k : ℕ) :
    Module.rank (S.H (k+1))ᵐᵒᵖ (StripSpace S k) = 2 := by
  rw [← (rightStripEquiv S k).rank_eq]
  have h : Module.rank (S.H (k+1))ᵐᵒᵖ (S.H (k+1)) = 1 := by
    let e : S.H (k+1) ≃ₗ[(S.H (k+1))ᵐᵒᵖ] (S.H (k+1))ᵐᵒᵖ := {
      toFun := MulOpposite.op
      invFun := MulOpposite.unop
      left_inv := MulOpposite.unop_op
      right_inv := MulOpposite.op_unop
      map_add' := MulOpposite.op_add
      map_smul' r x := rfl }
    rw [e.rank_eq, Module.rank_self]
  rw [rank_fun_eq_lift_mul, h]
  simp

theorem iterated_right_dual_rank (S : FlagSystem D) (k : ℕ) :
    Module.rank (iteratedRightDual (ambientBimodule (S.H 1)) (k+1)).RightRingᵐᵒᵖ
      (iteratedRightDual (ambientBimodule (S.H 1)) (k+1)).Space = 2 := by
  rw [(iteratedDualStripEquivalence S k).right_rank_eq]
  exact strip_right_rank S k

theorem ambient_right_rank_one (H : Subfield D) :
    Module.rank (ambientBimodule H).RightRingᵐᵒᵖ (ambientBimodule H).Space = 1 := by
  change Module.rank Dᵐᵒᵖ D = 1
  let e : D ≃ₗ[Dᵐᵒᵖ] Dᵐᵒᵖ := {
      toFun := MulOpposite.op
      invFun := MulOpposite.unop
      left_inv := MulOpposite.unop_op
      right_inv := MulOpposite.op_unop
      map_add' := MulOpposite.op_add
      map_smul' r x := rfl }
  rw [e.rank_eq, Module.rank_self]

theorem iterated_right_dual_finite (S : FlagSystem D) (n : ℕ) :
    FiniteDimensional (iteratedRightDual (ambientBimodule (S.H 1)) n).RightRingᵐᵒᵖ
      (iteratedRightDual (ambientBimodule (S.H 1)) n).Space := by
  cases n with
  | zero => exact Module.finite_of_rank_eq_nat (n := 1) (ambient_right_rank_one (S.H 1))
  | succ k => exact Module.finite_of_rank_eq_nat (n := 2) (iterated_right_dual_rank S k)

/-- The actual iterated right duals have the dimension sequence (1,2,2,...). -/
theorem right_dimension_sequence (S : FlagSystem D) (n : ℕ) :
    Module.finrank (iteratedRightDual (ambientBimodule (S.H 1)) n).RightRingᵐᵒᵖ
      (iteratedRightDual (ambientBimodule (S.H 1)) n).Space = if n = 0 then 1 else 2 := by
  cases n with
  | zero => exact Module.finrank_eq_of_rank_eq (n := 1) (ambient_right_rank_one (S.H 1))
  | succ k =>
    rw [if_neg (by omega)]
    exact Module.finrank_eq_of_rank_eq (iterated_right_dual_rank S k)

theorem actual_right_dimension_sequence (n : ℕ) :
    Module.finrank (iteratedRightDual (ambientBimodule (actualFlagSystem.H 1)) n).RightRingᵐᵒᵖ
      (iteratedRightDual (ambientBimodule (actualFlagSystem.H 1)) n).Space =
        if n = 0 then 1 else 2 :=
  right_dimension_sequence actualFlagSystem n

end

end QuantumFlags

import QuantumFlags.WideMatrices
import Mathlib.Algebra.Polynomial.Eval.Degree

namespace QuantumFlags

open Polynomial

noncomputable def positivePoly : ℕ → ℚ[X]
  | 0 => 1
  | r+1 => positivePoly r * (1 + C ((1/2 : ℚ)^r)*X)

noncomputable def quantumPoly : ℕ → ℚ[X]
  | 0 => 1
  | r+1 => quantumPoly r * (1 - C ((1/2 : ℚ)^r)*X)

theorem positivePoly_coeff_zero (r : ℕ) : (positivePoly r).coeff 0 = 1 := by
  induction r with
  | zero => simp [positivePoly]
  | succ r ih => simp [positivePoly, mul_add, ← mul_assoc, ih]

theorem quantumPoly_coeff_zero (r : ℕ) : (quantumPoly r).coeff 0 = 1 := by
  induction r with
  | zero => simp [quantumPoly]
  | succ r ih => simp [quantumPoly, mul_sub, ← mul_assoc, ih]

theorem positivePoly_coeff_succ (r k : ℕ) :
    (positivePoly (r+1)).coeff (k+1) =
      (positivePoly r).coeff (k+1) + (positivePoly r).coeff k * (1/2 : ℚ)^r := by
  simp [positivePoly, mul_add, ← mul_assoc, coeff_mul_X, coeff_mul_C]

theorem quantumPoly_coeff_succ (r k : ℕ) :
    (quantumPoly (r+1)).coeff (k+1) =
      (quantumPoly r).coeff (k+1) - (quantumPoly r).coeff k * (1/2 : ℚ)^r := by
  simp [quantumPoly, mul_sub, ← mul_assoc, coeff_mul_X, coeff_mul_C]

theorem positivePoly_coeff_nonnegative (r k : ℕ) : 0 ≤ (positivePoly r).coeff k := by
  induction r generalizing k with
  | zero => simp [positivePoly, coeff_one]; split_ifs <;> norm_num
  | succ r ih =>
    cases k with
    | zero => rw [positivePoly_coeff_zero]; norm_num
    | succ k =>
      rw [positivePoly_coeff_succ]
      exact add_nonneg (ih _) (mul_nonneg (ih _) (pow_nonneg (by norm_num) _))

theorem positivePoly_coeff_positive (r k : ℕ) (hk : k ≤ r) :
    0 < (positivePoly r).coeff k := by
  induction r generalizing k with
  | zero =>
    have h : k = 0 := Nat.eq_zero_of_le_zero hk
    simp [h, positivePoly]
  | succ r ih =>
    cases k with
    | zero => rw [positivePoly_coeff_zero]; norm_num
    | succ k =>
      rw [positivePoly_coeff_succ]
      exact add_pos_of_nonneg_of_pos (positivePoly_coeff_nonnegative _ _)
        (mul_pos (ih k (Nat.le_of_succ_le_succ hk)) (pow_pos (by norm_num) _))

theorem quantumPoly_coeff_sign (r k : ℕ) :
    (quantumPoly r).coeff k = (-1 : ℚ)^k * (positivePoly r).coeff k := by
  induction r generalizing k with
  | zero => cases k <;> simp [quantumPoly, positivePoly, coeff_one]
  | succ r ih =>
    cases k with
    | zero => simp [quantumPoly_coeff_zero, positivePoly_coeff_zero]
    | succ k =>
      rw [quantumPoly_coeff_succ, positivePoly_coeff_succ, ih, ih, pow_succ]
      ring

theorem quantumPoly_coeff_nonzero (r k : ℕ) (hk : k ≤ r) :
    (quantumPoly r).coeff k ≠ 0 := by
  rw [quantumPoly_coeff_sign]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num))
    (ne_of_gt (positivePoly_coeff_positive r k hk))

theorem positivePoly_coeff_above (r k : ℕ) (hk : r < k) :
    (positivePoly r).coeff k = 0 := by
  induction r generalizing k with
  | zero => simp [positivePoly, coeff_one, Nat.ne_of_gt hk]
  | succ r ih =>
    cases k with
    | zero => exact False.elim (Nat.not_lt_zero _ hk)
    | succ k =>
      rw [positivePoly_coeff_succ, ih _ (Nat.lt_of_succ_lt_succ hk),
        ih _ (Nat.lt_trans (Nat.lt_of_succ_lt_succ hk) (Nat.lt_succ_self _))]
      simp

theorem quantumPoly_natDegree_le (r : ℕ) : (quantumPoly r).natDegree ≤ r := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [quantumPoly_coeff_sign, positivePoly_coeff_above r k hk, mul_zero]

variable {D : Type*} [DivisionRing D] [CharZero D]

theorem quantumPoly_eval (r : ℕ) (v : D) :
    (quantumPoly r).eval₂ (Rat.castHom D) v = poch (half D) r v := by
  induction r with
  | zero => simp [quantumPoly, poch]
  | succ r ih =>
    rw [quantumPoly, Polynomial.eval₂_mul_noncomm]
    · simp only [Polynomial.eval₂_sub, Polynomial.eval₂_one, Polynomial.eval₂_C,
        Polynomial.eval₂_mul_X]
      rw [ih]
      change poch (half D) r v * (1-((((1/2 : ℚ)^r : ℚ) : D))*v) = _
      rw [cast_half_pow]
      rfl
    · intro k
      exact Rat.cast_commute _ v

/-- All coefficients in the actual degree-r Pochhammer polynomial are nonzero,
and the polynomial evaluates to the ordered product in every division ring. -/
theorem poch_coefficient_expansion (r : ℕ) (v : D) :
    poch (half D) r v =
      ∑ k ∈ Finset.range (r+1), (((quantumPoly r).coeff k : ℚ) : D)*v^k := by
  rw [← quantumPoly_eval]
  exact Polynomial.eval₂_eq_sum_range' (Rat.castHom D)
    (Nat.lt_succ_of_le (quantumPoly_natDegree_le r)) v

end QuantumFlags

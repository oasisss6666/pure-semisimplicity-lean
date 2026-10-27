import QuantumFlags.MatrixCore
import QuantumFlags.OrderedPochhammer
import Mathlib.Tactic.NoncommRing

namespace QuantumFlags

variable {D : Type*} [DivisionRing D] [CharZero D]

/-- The only non-vanishing hypothesis used in this local block.
It is implied by the manuscript's stronger PBW transcendence statement. -/
def NotRational (v : D) : Prop := ∀ r : ℚ, v ≠ (r : D)

theorem linear_factor_ne_zero (v : D) (hv : NotRational v) (c : ℚ) :
    1 - (c : D)*v ≠ 0 := by
  by_cases hc : c = 0
  · simp [hc]
  have hcD : (c : D) ≠ 0 := by exact_mod_cast hc
  intro h
  have hcv : (c : D)*v = 1 := (sub_eq_zero.mp h).symm
  have hh := congrArg (fun z : D => (c : D)⁻¹*z) hcv
  apply hv c⁻¹
  simpa only [inv_mul_cancel_left₀ hcD, mul_one, Rat.cast_inv] using hh

theorem rat_mul_notRational (v : D) (hv : NotRational v) (c : ℚ) (hc : c ≠ 0) :
    NotRational ((c : D)*v) := by
  have hcD : (c : D) ≠ 0 := by exact_mod_cast hc
  intro r h
  have hh := congrArg (fun z : D => (c : D)⁻¹*z) h
  apply hv (c⁻¹*r)
  simpa only [inv_mul_cancel_left₀ hcD, Rat.cast_mul, Rat.cast_inv] using hh

theorem poch_ne_zero (v : D) (hv : NotRational v) (q : ℚ) (n : ℕ) :
    poch (q : D) n v ≠ 0 := by
  induction n with
  | zero => exact one_ne_zero
  | succ n ih =>
    apply mul_ne_zero ih
    have hcast : ((q^n : ℚ) : D) = (q : D)^n := map_pow (Rat.castHom D) q n
    rw [← hcast]
    exact linear_factor_ne_zero v hv (q^n)

def half (D : Type*) [DivisionRing D] : D := ((1/2 : ℚ) : D)

theorem cast_half_pow (p : ℕ) : ((((1/2 : ℚ)^p : ℚ) : D)) = (half D)^p := by
  induction p with
  | zero => simp
  | succ p ih =>
    simp only [pow_succ, Rat.cast_mul, ih, half]

theorem right_strip_half (v x a b : D) (hv : NotRational v)
    (hvx : v*x = half D*x*v) (hav : Commute a v) (hbv : Commute b v) (p : ℕ) :
    (poch (half D) p v)⁻¹ * (a+x*b) * poch (half D) (p+1) v =
      (1-(half D)^p*v)*a + (1-(2 : D)*v)*x*b := by
  have hq : half D ≠ 0 := by norm_num [half]
  have hxq : Commute x (half D) := (Rat.cast_commute _ x).symm
  have hxv : x*v = ((half D)⁻¹*v)*x := by
    have h := congrArg (fun z : D => (half D)⁻¹*z) hvx
    simpa only [mul_assoc, inv_mul_cancel_left₀ hq] using h.symm
  have hqi : (half D)⁻¹ = (2 : D) := by norm_num [half]
  simpa only [hqi] using
    right_strip_recursion (half D) v x a b hq (Rat.cast_commute _ v) hxq hxv
      (Rat.cast_commute _ a).symm hav (Rat.cast_commute _ b).symm hbv p
      (poch_ne_zero v hv (1/2) p)

theorem left_strip_half (v x a b : D) (hv : NotRational v)
    (hvx : v*x = half D*x*v) (hav : Commute a v) (hbv : Commute b v) (p : ℕ) :
    (poch (half D) p v)⁻¹ * (a+b*x) * poch (half D) (p+1) v =
      a*(1-(half D)^p*v) + b*x*(1-v) := by
  have hq : half D ≠ 0 := by norm_num [half]
  have hxq : Commute x (half D) := (Rat.cast_commute _ x).symm
  have hvx' : v*x = x*(half D*v) := by
    calc
      v*x = half D*x*v := hvx
      _ = x*(half D*v) := by rw [hxq.symm.eq, mul_assoc]
  exact left_strip_recursion (half D) v x a b hq (Rat.cast_commute _ v) hxq hvx'
    (Rat.cast_commute _ a).symm hav (Rat.cast_commute _ b).symm hbv p
    (poch_ne_zero v hv (1/2) p)
    (poch_ne_zero _ (rat_mul_notRational v hv (1/2) (by norm_num)) (1/2) p)

def rightCoordinate (v : D) (M : Mat2 D) (i : Fin 2) : D := M 0 i + v*M 1 i
def leftCoordinate (M : Mat2 D) (v : D) (i : Fin 2) : D := M i 0 + M i 1*v

theorem rightCoordinate_step (a b : ℚ) (v x : D) (M : Mat2 D) (i : Fin 2) :
    rightCoordinate v (liftRat (rightCoeff a b) * diagUnit x * M) i =
      (1-(a : D)*v)*M 0 i + (1-(b : D)*v)*x*M 1 i := by
  simp [rightCoordinate, liftRat, rightCoeff, diagUnit, Matrix.mul_apply,
    Fin.sum_univ_two, Rat.castHom]
  noncomm_ring [(Rat.cast_commute a v).symm.left_comm,
    (Rat.cast_commute b v).symm.left_comm]

theorem leftCoordinate_step (a : ℚ) (v x : D) (M : Mat2 D) (i : Fin 2) :
    leftCoordinate (M * diagUnit x * liftRat (leftCoeff a)) v i =
      M i 0*(1-(a : D)*v) + M i 1*x*(1-v) := by
  simp [leftCoordinate, liftRat, leftCoeff, diagUnit, Matrix.mul_apply,
    Fin.sum_univ_two]
  noncomm_ring

/-- The right matrix update is the actual local conjugation, not merely
an unrelated invertible matrix with the same dimensions. -/
theorem right_local_flag_step (v x : D) (hv : NotRational v)
    (hvx : v*x = half D*x*v) (M : Mat2 D) (i : Fin 2)
    (h0 : Commute (M 0 i) v) (h1 : Commute (M 1 i) v) (p : ℕ) :
    rightCoordinate v (rightStep p * diagUnit x * M) i =
      (poch (half D) p v)⁻¹ * rightCoordinate x M i * poch (half D) (p+1) v := by
  rw [rightStep, rightCoordinate_step]
  have hcast := cast_half_pow (D := D) p
  erw [hcast]
  simpa [rightCoordinate] using
    (right_strip_half v x (M 0 i) (M 1 i) hv hvx h0 h1 p).symm

/-- The left matrix update realizes the same local conjugation in its own
coefficient orientation, without transposing a noncommutative matrix. -/
theorem left_local_flag_step (v x : D) (hv : NotRational v)
    (hvx : v*x = half D*x*v) (M : Mat2 D) (i : Fin 2)
    (h0 : Commute (M i 0) v) (h1 : Commute (M i 1) v) (p : ℕ) :
    leftCoordinate (M * diagUnit x * leftStep p) v i =
      (poch (half D) p v)⁻¹ * leftCoordinate M x i * poch (half D) (p+1) v := by
  rw [leftStep, leftCoordinate_step]
  have hcast := cast_half_pow (D := D) p
  erw [hcast]
  simpa [leftCoordinate] using
    (left_strip_half v x (M i 0) (M i 1) hv hvx h0 h1 p).symm

omit [CharZero D] in
/-- Inverse matrices give genuine bijections on right coordinate columns. -/
theorem HasInverse.mulVec_bijective {M : Mat2 D} (hM : HasInverse M) :
    Function.Bijective M.mulVec := by
  obtain ⟨B, hMB, hBM⟩ := hM
  constructor
  · intro u v h
    have hh := congrArg B.mulVec h
    simpa only [Matrix.mulVec_mulVec, hBM, Matrix.one_mulVec] using hh
  · intro v
    refine ⟨B.mulVec v, ?_⟩
    rw [Matrix.mulVec_mulVec, hMB, Matrix.one_mulVec]

omit [CharZero D] in
/-- Separately, inverse matrices give bijections on left coordinate rows. -/
theorem HasInverse.vecMul_bijective {M : Mat2 D} (hM : HasInverse M) :
    Function.Bijective (fun v => Matrix.vecMul v M) := by
  obtain ⟨B, hMB, hBM⟩ := hM
  constructor
  · intro u v h
    have hh := congrArg (fun w => Matrix.vecMul w B) h
    simpa only [Matrix.vecMul_vecMul, hMB, Matrix.vecMul_one] using hh
  · intro v
    refine ⟨Matrix.vecMul v B, ?_⟩
    change Matrix.vecMul (Matrix.vecMul v B) M = v
    rw [Matrix.vecMul_vecMul, hBM, Matrix.vecMul_one]

/-- For every finite layer, both ordered coordinate maps are bijective.
This is universal in the layer n and parameter p >= 1. -/
theorem all_layers_coordinate_bijections (p : ℕ) (hp : 1 ≤ p)
    (x : ℕ → D) (hx : ∀ n, x n ≠ 0) (n : ℕ) :
    Function.Bijective (rightRecursion p x n).mulVec ∧
    Function.Bijective (fun v => Matrix.vecMul v (leftRecursion p x n)) := by
  exact ⟨(rightRecursion_hasInverse p hp x hx n).mulVec_bijective,
    (leftRecursion_hasInverse p hp x hx n).vecMul_bijective⟩

end QuantumFlags

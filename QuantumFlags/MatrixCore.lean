import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Order.Field.Power

/-!
The two ordered 2-by-2 recursions in manuscript Section 4.
The coefficient division ring is not assumed commutative.
-/

namespace QuantumFlags

abbrev Mat2 (D : Type*) := Matrix (Fin 2) (Fin 2) D

/-- An explicit two-sided inverse, with no determinant over a noncommutative ring. -/
def HasInverse {D : Type*} [Semiring D] (A : Mat2 D) : Prop :=
  ∃ B : Mat2 D, A * B = 1 ∧ B * A = 1

theorem hasInverse_one {D : Type*} [Semiring D] : HasInverse (1 : Mat2 D) :=
  ⟨1, by simp, by simp⟩

theorem HasInverse.mul {D : Type*} [Semiring D] {A B : Mat2 D}
    (hA : HasInverse A) (hB : HasInverse B) : HasInverse (A * B) := by
  obtain ⟨A', hAA', hA'A⟩ := hA
  obtain ⟨B', hBB', hB'B⟩ := hB
  refine ⟨B' * A', ?_, ?_⟩
  · calc
      (A * B) * (B' * A') = A * (B * B') * A' := by simp [mul_assoc]
      _ = 1 := by rw [hBB']; simpa using hAA'
  · calc
      (B' * A') * (A * B) = B' * (A' * A) * B := by simp [mul_assoc]
      _ = 1 := by rw [hA'A]; simpa using hB'B

def rightCoeff (a b : ℚ) : Mat2 ℚ := !![1, 1; -a, -b]
def rightCoeffInv (a b : ℚ) : Mat2 ℚ :=
  !![-b / (a-b), -1 / (a-b); a / (a-b), 1 / (a-b)]

theorem rightCoeff_hasInverse (a b : ℚ) (hab : a ≠ b) :
    HasInverse (rightCoeff a b) := by
  have hd : a - b ≠ 0 := sub_ne_zero.mpr hab
  refine ⟨rightCoeffInv a b, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [rightCoeff, rightCoeffInv, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring

def leftCoeff (a : ℚ) : Mat2 ℚ := !![1, -a; 1, -1]
def leftCoeffInv (a : ℚ) : Mat2 ℚ :=
  !![-1 / (a-1), a / (a-1); -1 / (a-1), 1 / (a-1)]

theorem leftCoeff_hasInverse (a : ℚ) (ha : a ≠ 1) :
    HasInverse (leftCoeff a) := by
  have hd : a - 1 ≠ 0 := sub_ne_zero.mpr ha
  refine ⟨leftCoeffInv a, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [leftCoeff, leftCoeffInv, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring

def liftRat {D : Type*} [DivisionRing D] [CharZero D] (A : Mat2 ℚ) : Mat2 D :=
  A.map (Rat.castHom D)

theorem HasInverse.mapRat {D : Type*} [DivisionRing D] [CharZero D]
    {A : Mat2 ℚ} (hA : HasInverse A) : HasInverse (liftRat (D := D) A) := by
  obtain ⟨B, hAB, hBA⟩ := hA
  refine ⟨liftRat B, ?_, ?_⟩
  · change A.map (Rat.castHom D) * B.map (Rat.castHom D) = 1
    rw [← Matrix.map_mul, hAB]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  · change B.map (Rat.castHom D) * A.map (Rat.castHom D) = 1
    rw [← Matrix.map_mul, hBA]
    exact Matrix.map_one _ (map_zero _) (map_one _)

def diagUnit {D : Type*} [Zero D] [One D] (x : D) : Mat2 D := !![1, 0; 0, x]

theorem diagUnit_hasInverse {D : Type*} [DivisionRing D] (x : D) (hx : x ≠ 0) :
    HasInverse (diagUnit x) := by
  refine ⟨diagUnit x⁻¹, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [diagUnit, Matrix.mul_apply, Fin.sum_univ_two, hx]

/-- The right coefficient matrix C_p, for the actual parameter q = 1/2. -/
def rightStep {D : Type*} [DivisionRing D] [CharZero D] (p : ℕ) : Mat2 D :=
  liftRat (rightCoeff ((1/2 : ℚ)^p) 2)

/-- The separate left coefficient matrix D_p; no transpose is used. -/
def leftStep {D : Type*} [DivisionRing D] [CharZero D] (p : ℕ) : Mat2 D :=
  liftRat (leftCoeff ((1/2 : ℚ)^p))

theorem half_pow_lt_one (p : ℕ) (hp : 1 ≤ p) : (1/2 : ℚ)^p < 1 := by
  exact pow_lt_one₀ (by norm_num) (by norm_num) (Nat.ne_of_gt hp)

theorem rightStep_hasInverse {D : Type*} [DivisionRing D] [CharZero D]
    (p : ℕ) (hp : 1 ≤ p) : HasInverse (rightStep (D := D) p) := by
  apply HasInverse.mapRat
  apply rightCoeff_hasInverse
  exact ne_of_lt (lt_trans (half_pow_lt_one p hp) (by norm_num))

theorem leftStep_hasInverse {D : Type*} [DivisionRing D] [CharZero D]
    (p : ℕ) (hp : 1 ≤ p) : HasInverse (leftStep (D := D) p) := by
  exact (leftCoeff_hasInverse _ (ne_of_lt (half_pow_lt_one p hp))).mapRat

def rightRecursion {D : Type*} [DivisionRing D] [CharZero D]
    (p : ℕ) (x : ℕ → D) : ℕ → Mat2 D
  | 0 => 1
  | n+1 => rightStep p * diagUnit (x n) * rightRecursion p x n

def leftRecursion {D : Type*} [DivisionRing D] [CharZero D]
    (p : ℕ) (x : ℕ → D) : ℕ → Mat2 D
  | 0 => 1
  | n+1 => leftRecursion p x n * diagUnit (x n) * leftStep p

/-- The manuscript's right coordinate recursion is invertible at every finite layer. -/
theorem rightRecursion_hasInverse {D : Type*} [DivisionRing D] [CharZero D]
    (p : ℕ) (hp : 1 ≤ p) (x : ℕ → D) (hx : ∀ n, x n ≠ 0) (n : ℕ) :
    HasInverse (rightRecursion p x n) := by
  induction n with
  | zero => exact hasInverse_one
  | succ n ih => exact ((rightStep_hasInverse p hp).mul
      (diagUnit_hasInverse (x n) (hx n))).mul ih

/-- The distinct left recursion is also invertible at every finite layer. -/
theorem leftRecursion_hasInverse {D : Type*} [DivisionRing D] [CharZero D]
    (p : ℕ) (hp : 1 ≤ p) (x : ℕ → D) (hx : ∀ n, x n ≠ 0) (n : ℕ) :
    HasInverse (leftRecursion p x n) := by
  induction n with
  | zero => exact hasInverse_one
  | succ n ih =>
    exact (ih.mul (diagUnit_hasInverse (x n) (hx n))).mul (leftStep_hasInverse p hp)

end QuantumFlags

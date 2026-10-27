import QuantumFlags.GlobalFlags
import Mathlib.LinearAlgebra.Vandermonde

namespace QuantumFlags

variable {D : Type*} [DivisionRing D]
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A two-sided inverse for a square matrix of any finite size. -/
def FullInverse (A : Matrix I I D) : Prop :=
  ∃ B : Matrix I I D, A*B=1 ∧ B*A=1

theorem FullInverse.mul {A B : Matrix I I D}
    (hA : FullInverse A) (hB : FullInverse B) : FullInverse (A*B) := by
  obtain ⟨A', hAA', hA'A⟩ := hA
  obtain ⟨B', hBB', hB'B⟩ := hB
  refine ⟨B'*A', ?_, ?_⟩
  · calc
      (A*B)*(B'*A') = A*(B*B')*A' := by simp [mul_assoc]
      _ = 1 := by rw [hBB']; simpa using hAA'
  · calc
      (B'*A')*(A*B) = B'*(A'*A)*B := by simp [mul_assoc]
      _ = 1 := by rw [hA'A]; simpa using hB'B

theorem FullInverse.map {K : Type*} [DivisionRing K] (ι : K →+* D)
    {A : Matrix I I K} (hA : FullInverse A) : FullInverse (A.map ι) := by
  obtain ⟨B, hAB, hBA⟩ := hA
  refine ⟨B.map ι, ?_, ?_⟩
  · rw [← Matrix.map_mul, hAB]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  · rw [← Matrix.map_mul, hBA]
    exact Matrix.map_one _ (map_zero _) (map_one _)

theorem fullInverse_diagonal (d : I → D) (hd : ∀ i, d i ≠ 0) :
    FullInverse (Matrix.diagonal d) := by
  refine ⟨Matrix.diagonal (fun i => (d i)⁻¹), ?_, ?_⟩ <;>
    rw [Matrix.diagonal_mul_diagonal] <;> ext i j <;>
    by_cases h : i = j <;> simp [Matrix.one_apply, h, hd]

theorem FullInverse.mulVec_bijective {A : Matrix I I D} (hA : FullInverse A) :
    Function.Bijective A.mulVec := by
  obtain ⟨B, hAB, hBA⟩ := hA
  constructor
  · intro c d h
    have hh := congrArg B.mulVec h
    simpa only [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec] using hh
  · intro c
    exact ⟨B.mulVec c, by rw [Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]⟩

def rationalVandermonde (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.vandermonde (fun k => (2 : ℚ)^k.val)

theorem rationalVandermonde_hasInverse (n : ℕ) : FullInverse (rationalVandermonde n) := by
  have hn : Function.Injective (fun k : Fin n => (2 : ℚ)^k.val) := by
    intro i j h
    exact Fin.ext ((pow_right_strictMono₀ (by norm_num : (1 : ℚ) < 2)).injective h)
  have hd : IsUnit (rationalVandermonde n).det :=
    isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hn)
  exact ⟨(rationalVandermonde n)⁻¹, Matrix.mul_nonsing_inv _ hd,
    Matrix.nonsing_inv_mul _ hd⟩

variable [CharZero D]

def wideVandermonde (n : ℕ) : Matrix (Fin n) (Fin n) D :=
  (rationalVandermonde n).map (Rat.castHom D)

theorem wideVandermonde_hasInverse (n : ℕ) : FullInverse (wideVandermonde (D := D) n) :=
  (rationalVandermonde_hasInverse n).map (Rat.castHom D)

def wideDenominator (r : ℕ) (v : D) : Matrix (Fin (r+1)) (Fin (r+1)) D :=
  Matrix.diagonal (fun k => poch (half D) r ((((2 : ℚ)^k.val : ℚ) : D)*v))

def wideDenominatorInv (r : ℕ) (v : D) : Matrix (Fin (r+1)) (Fin (r+1)) D :=
  Matrix.diagonal (fun k => (poch (half D) r ((((2 : ℚ)^k.val : ℚ) : D)*v))⁻¹)

theorem wideDenominator_nonzero (r : ℕ) (v : D) (hv : NotRational v) (k : Fin (r+1)) :
    poch (half D) r ((((2 : ℚ)^k.val : ℚ) : D)*v) ≠ 0 := by
  exact poch_ne_zero _ (rat_mul_notRational v hv _ (pow_ne_zero _ (by norm_num))) (1/2) r

theorem wideDenominator_hasInverse (r : ℕ) (v : D) (hv : NotRational v) :
    FullInverse (wideDenominator r v) :=
  fullInverse_diagonal _ (wideDenominator_nonzero r v hv)

theorem wideDenominatorInv_hasInverse (r : ℕ) (v : D) (hv : NotRational v) :
    FullInverse (wideDenominatorInv r v) :=
  fullInverse_diagonal _ (fun k => inv_ne_zero (wideDenominator_nonzero r v hv k))

theorem wideDenominator_cancels (r : ℕ) (v : D) (hv : NotRational v) :
    wideDenominator r v * wideDenominatorInv r v = 1 ∧
    wideDenominatorInv r v * wideDenominator r v = 1 := by
  constructor <;> unfold wideDenominator wideDenominatorInv <;>
    rw [Matrix.diagonal_mul_diagonal] <;> ext i j <;> by_cases h : i = j <;>
    simp [Matrix.one_apply, h, wideDenominator_nonzero r v hv]

def wideCoefficientDiagonal (r : ℕ) (d : Fin (r+1) → ℚ) (v : D) :
    Matrix (Fin (r+1)) (Fin (r+1)) D :=
  Matrix.diagonal (fun h => (d h : D)*v^h.val)

theorem wideCoefficientDiagonal_hasInverse (r : ℕ) (d : Fin (r+1) → ℚ)
    (hd : ∀ h, d h ≠ 0) (v : D) (hv : v ≠ 0) :
    FullInverse (wideCoefficientDiagonal r d v) := by
  apply fullInverse_diagonal
  intro h
  apply mul_ne_zero
  · exact_mod_cast hd h
  · exact pow_ne_zero _ hv

/-- The ordered A-matrix recursion, before its identification with the
automorphism coordinates in equation (Arec). -/
def wideRecursion (r : ℕ) (d : Fin (r+1) → ℚ) (x : ℕ → D) :
    ℕ → Matrix (Fin (r+1)) (Fin (r+1)) D
  | 0 => wideVandermonde (r+1) * Matrix.diagonal (fun i => (x 0)^i.val)
  | n+1 => wideDenominatorInv r (x (n+1)) * wideVandermonde (r+1) *
      wideCoefficientDiagonal r d (x (n+1)) * wideRecursion r d x n

theorem wideRecursion_hasInverse (r : ℕ) (d : Fin (r+1) → ℚ)
    (hd : ∀ h, d h ≠ 0) (x : ℕ → D) (hx : ∀ n, NotRational (x n)) (n : ℕ) :
    FullInverse (wideRecursion r d x n) := by
  induction n with
  | zero =>
    exact (wideVandermonde_hasInverse (D := D) _).mul
      (fullInverse_diagonal _ (fun i => pow_ne_zero _ (notRational_ne_zero (hx 0))))
  | succ n ih =>
    exact (((wideDenominatorInv_hasInverse _ _ (hx (n+1))).mul
      (wideVandermonde_hasInverse _)).mul
      (wideCoefficientDiagonal_hasInverse _ d hd _ (notRational_ne_zero (hx (n+1))))).mul ih

theorem wideRecursion_equation (r : ℕ) (d : Fin (r+1) → ℚ) (x : ℕ → D)
    (hx : ∀ n, NotRational (x n)) (n : ℕ) :
    wideDenominator r (x (n+1)) * wideRecursion r d x (n+1) =
      wideVandermonde (r+1) * wideCoefficientDiagonal r d (x (n+1)) *
        wideRecursion r d x n := by
  simp only [wideRecursion, ← mul_assoc, (wideDenominator_cancels r _ (hx (n+1))).1,
    one_mul]

end QuantumFlags

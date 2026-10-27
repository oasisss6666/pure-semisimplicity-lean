import QuantumFlags.SkewFiniteSpaces
import QuantumFlags.Coordinates
import Mathlib.RingTheory.OreLocalization.Ring
import Mathlib.RingTheory.OreLocalization.OreSet

namespace QuantumFlags

noncomputable section

open scoped nonZeroDivisors
open OreLocalization

variable {K : Type*} [DivisionRing K] [MulSemiringAction (Multiplicative ℕ) K]

theorem skew_ore_condition (p : SkewPolynomial K) (s : (SkewPolynomial K)⁰) :
    ∃ (r' : SkewPolynomial K) (s' : (SkewPolynomial K)⁰), s'*p=r'*s := by
  by_cases hp : p = 0
  · exact ⟨0, 1, by simp [hp]⟩
  · obtain ⟨X, Y, hX, _, hXY⟩ := skew_common_left_multiple p (s : SkewPolynomial K)
      hp (nonZeroDivisors.coe_ne_zero s)
    exact ⟨Y, ⟨X, mem_nonZeroDivisors_of_ne_zero hX⟩, hXY⟩

instance skewPolynomial_oreSet : OreSet (SkewPolynomial K)⁰ :=
  Classical.choice (nonempty_oreSet_iff_of_noZeroDivisors.mpr skew_ore_condition)

/-- An actual Ore division ring, rather than a parameter asserting that a
fraction division ring exists. Its multiplication is the skew multiplication
specified by the given monoid action on K. -/
abbrev SkewFractions (K : Type*) [DivisionRing K]
    [MulSemiringAction (Multiplicative ℕ) K] :=
  OreLocalization ((SkewPolynomial K)⁰) (SkewPolynomial K)

def skewNumerator : SkewPolynomial K →+* SkewFractions K := numeratorRingHom

def skewConstants : K →+* SkewFractions K :=
  skewNumerator.comp SkewPolynomial.CRingHom

def skewVariable : SkewFractions K := skewNumerator (SkewPolynomial.X : SkewPolynomial K)

theorem skewNumerator_injective : Function.Injective (skewNumerator (K := K)) :=
  numeratorHom_inj inf_le_left

theorem skewConstants_injective : Function.Injective (skewConstants (K := K)) :=
  (skewConstants (K := K)).injective

theorem skew_variable_relation (a : K) :
    skewVariable * skewConstants a =
      skewConstants (SkewPolynomial.φ a) * skewVariable := by
  have hp : (SkewPolynomial.X : SkewPolynomial K)*SkewPolynomial.C a =
      SkewPolynomial.C (SkewPolynomial.φ a)*SkewPolynomial.X := by
    rw [← SkewPolynomial.monomial_zero_left, SkewPolynomial.X_mul_monomial]
    rw [SkewPolynomial.C_mul_X_eq_monomial]
  change skewNumerator SkewPolynomial.X * skewNumerator (SkewPolynomial.C a) =
    skewNumerator (SkewPolynomial.C (SkewPolynomial.φ a)) * skewNumerator SkewPolynomial.X
  rw [← map_mul, ← map_mul, hp]

theorem skewOfCoefficients_injective (r : ℕ) :
    Function.Injective (skewOfCoefficients (K := K) r) := by
  intro c d h
  funext i
  have he := congrArg (fun p : SkewPolynomial K => SkewPolynomial.coeff p i.val) h
  simpa only [skewOfCoefficients_coeff_le r _ i.val (Nat.le_of_lt_succ i.isLt)] using he

def skewLeftPowerEval (r : ℕ) (c : Fin (r+1) → K) : SkewFractions K :=
  ∑ i, skewConstants (c i)*skewVariable^i.val

def skewRightPowerEval (r : ℕ) (c : Fin (r+1) → K) : SkewFractions K :=
  ∑ i, skewVariable^i.val*skewConstants (c i)

theorem skew_left_power_polynomial (r : ℕ) (c : Fin (r+1) → K) :
    skewLeftPowerEval r c = skewNumerator (skewOfCoefficients r c) := by
  simp only [skewLeftPowerEval, skewOfCoefficients, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← SkewPolynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
  rfl

theorem skew_right_power_polynomial (r : ℕ) (c : Fin (r+1) → K) :
    skewRightPowerEval r c = skewNumerator
      (skewOfCoefficients r (fun i => (SkewPolynomial.φ^[i.val]) (c i))) := by
  simp only [skewRightPowerEval, skewOfCoefficients, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : (SkewPolynomial.X : SkewPolynomial K)^i.val*SkewPolynomial.C (c i) =
      SkewPolynomial.monomial i.val ((SkewPolynomial.φ^[i.val]) (c i)) := by
    rw [← SkewPolynomial.monomial_zero_left, SkewPolynomial.X_pow_mul_monomial]
    simp
  rw [← he, map_mul, map_pow]
  rfl

theorem skew_left_powers_independent (r : ℕ) :
    Function.Injective (skewLeftPowerEval (K := K) r) := by
  intro c d h
  apply skewOfCoefficients_injective r
  apply skewNumerator_injective
  simpa only [skew_left_power_polynomial] using h

theorem skew_right_powers_independent (r : ℕ) :
    Function.Injective (skewRightPowerEval (K := K) r) := by
  intro c d h
  have he : (fun i => (SkewPolynomial.φ^[i.val]) (c i)) =
      (fun i => (SkewPolynomial.φ^[i.val]) (d i)) := by
    apply skewOfCoefficients_injective r
    apply skewNumerator_injective
    simpa only [skew_right_power_polynomial] using h
  funext i
  exact ((SkewPolynomial.φ : K →+* K).injective.iterate i.val) (congrFun he i)

theorem skewVariable_not_constant (a : K) : skewVariable ≠ skewConstants a := by
  intro h
  have hp : (SkewPolynomial.X : SkewPolynomial K) = SkewPolynomial.C a :=
    skewNumerator_injective h
  have he := congrArg (fun p : SkewPolynomial K => SkewPolynomial.coeff p 1) hp
  simpa using he

instance skewFractions_charZero [CharZero K] : CharZero (SkewFractions K) where
  cast_injective m n h := by
    have he : (m : K) = (n : K) := skewConstants_injective (by simpa only [map_natCast] using h)
    exact Nat.cast_injective he

theorem skewVariable_notRational [CharZero K] : NotRational (skewVariable (K := K)) := by
  intro r h
  apply skewVariable_not_constant (r : K)
  simpa only [map_ratCast] using h

end

end QuantumFlags

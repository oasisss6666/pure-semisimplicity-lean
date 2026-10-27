import QuantumFlags.SkewFractionMaps
import Mathlib.Algebra.Ring.Action.End

namespace QuantumFlags

noncomputable section

variable {K : Type*} [DivisionRing K]

abbrev automorphismAction (τ : K ≃+* K) : MulSemiringAction (Multiplicative ℕ) K :=
  MulSemiringAction.compHom K (powersHom (RingAut K) τ)

theorem automorphismAction_phi (τ : K ≃+* K) (a : K) :
    letI := automorphismAction τ
    SkewPolynomial.φ a = τ a := by
  change (τ ^ (1 : ℕ)) a = τ a
  rw [pow_one]

/-- The actual division ring of left fractions of K[X;τ]. -/
abbrev SkewExtension (K : Type*) [DivisionRing K] (τ : K ≃+* K) : Type _ :=
  letI := automorphismAction τ
  SkewFractions K

instance skewExtension_divisionRing (τ : K ≃+* K) : DivisionRing (SkewExtension K τ) := by
  letI := automorphismAction τ
  exact inferInstanceAs (DivisionRing (SkewFractions K))

instance skewExtension_charZero [CharZero K] (τ : K ≃+* K) : CharZero (SkewExtension K τ) := by
  letI := automorphismAction τ
  exact inferInstanceAs (CharZero (SkewFractions K))

def extensionConstants (τ : K ≃+* K) : K →+* SkewExtension K τ := by
  letI := automorphismAction τ
  exact skewConstants

def extensionVariable (τ : K ≃+* K) : SkewExtension K τ := by
  letI := automorphismAction τ
  exact skewVariable

theorem extension_variable_relation (τ : K ≃+* K) (a : K) :
    extensionVariable τ * extensionConstants τ a =
      extensionConstants τ (τ a) * extensionVariable τ := by
  letI := automorphismAction τ
  exact (skew_variable_relation a).trans (by rw [automorphismAction_phi]; rfl)

def extensionScalingAut (τ : K ≃+* K) (c : K) (hc : ∀ a : K, Commute c a)
    (hcnz : c ≠ 0) : SkewExtension K τ ≃+* SkewExtension K τ := by
  letI := automorphismAction τ
  exact fractionScalingAut c hc hcnz

theorem extensionScalingAut_constants (τ : K ≃+* K) (c : K)
    (hc : ∀ a : K, Commute c a) (hcnz : c ≠ 0) (a : K) :
    extensionScalingAut τ c hc hcnz (extensionConstants τ a) = extensionConstants τ a := by
  letI := automorphismAction τ
  exact fractionScalingAut_constants c hc hcnz a

theorem extensionScalingAut_variable (τ : K ≃+* K) (c : K)
    (hc : ∀ a : K, Commute c a) (hcnz : c ≠ 0) :
    extensionScalingAut τ c hc hcnz (extensionVariable τ) =
      extensionConstants τ c * extensionVariable τ := by
  letI := automorphismAction τ
  exact fractionScalingAut_variable c hc hcnz

theorem extensionVariable_notRational [CharZero K] (τ : K ≃+* K) :
    NotRational (extensionVariable τ) := by
  letI := automorphismAction τ
  exact skewVariable_notRational

theorem extension_left_powers_independent (τ : K ≃+* K) (r : ℕ) :
    Function.Injective (fun c : Fin (r+1) → K =>
      ∑ i, extensionConstants τ (c i) * extensionVariable τ ^ i.val) := by
  letI := automorphismAction τ
  exact skew_left_powers_independent r

theorem extension_right_powers_independent (τ : K ≃+* K) (r : ℕ) :
    Function.Injective (fun c : Fin (r+1) → K =>
      ∑ i, extensionVariable τ ^ i.val * extensionConstants τ (c i)) := by
  letI := automorphismAction τ
  exact skew_right_powers_independent r

end

end QuantumFlags

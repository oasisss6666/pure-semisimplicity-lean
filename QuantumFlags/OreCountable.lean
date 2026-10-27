import QuantumFlags.OreTower
import Mathlib.Data.Finsupp.Encodable

/-!
# Countability of the quantum division ring

The skew rational function division ring over a countable division ring is countable, so every
level `T_n` of the tower and the union `T` are countable.  This is used to show that the
triangular ring is not left pure semisimple.
-/

namespace QuantumFlags
noncomputable section

variable {K : Type*} [DivisionRing K]

theorem skewPolynomial_countable [Countable K] (τ : K ≃+* K) :
    letI := automorphismAction τ
    Countable (SkewPolynomial K) := by
  letI := automorphismAction τ
  haveI : Countable (Multiplicative ℕ) := inferInstanceAs (Countable ℕ)
  exact Function.Injective.countable (f := SkewMonoidAlgebra.coeff)
    (fun p q h => by cases p; cases q; simp only at h; rw [h])

theorem skewExtension_countable [Countable K] (τ : K ≃+* K) :
    Countable (SkewExtension K τ) := by
  letI := automorphismAction τ
  haveI : Countable (SkewPolynomial K) := skewPolynomial_countable τ
  change Countable (OreLocalization (nonZeroDivisors (SkewPolynomial K)) (SkewPolynomial K))
  exact Function.Surjective.countable (f := fun p : SkewPolynomial K × nonZeroDivisors (SkewPolynomial K) =>
    OreLocalization.oreDiv p.1 p.2) (fun x => by
      induction x using OreLocalization.ind with
      | c r s => exact ⟨(r, s), rfl⟩)

theorem oreLevel_countable (n : ℕ) : Countable (OreLevel n) := by
  induction n with
  | zero =>
    change Countable ℚ
    exact Function.Injective.countable (f := fun q : ℚ => (q.num, q.den))
      (fun a b h => Rat.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  | succ n ih =>
    haveI := ih
    exact skewExtension_countable (oreAutomorphism n)

/-- The union `T` of the quantum division rings is countable. -/
instance oreUnion_countable : Countable OreUnion := by
  haveI : ∀ n, Countable (OreLevel n) := oreLevel_countable
  exact Function.Surjective.countable (f := fun p : Σ n, OreLevel n => oreEmbed p.1 p.2)
    (fun a => by
      obtain ⟨n, b, rfl⟩ := DirectLimit.exists_eq_mk oreMap a
      exact ⟨⟨n, b⟩, rfl⟩)

end
end QuantumFlags

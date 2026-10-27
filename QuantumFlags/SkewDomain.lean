import Mathlib.Algebra.SkewPolynomial.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
Leading coefficients and the domain property for skew polynomials over an
arbitrary division ring. These results concern actual mathlib skew polynomials;
the Ore and PBW assumptions of QuantumChain are not used here.
-/

namespace QuantumFlags

noncomputable section

open SkewPolynomial Multiplicative

variable {K : Type*} [DivisionRing K]

def skewCoeffLinear (n : ℕ) : SkewPolynomial K →ₗ[K] K where
  toFun p := SkewPolynomial.coeff p n
  map_add' p q := SkewPolynomial.coeff_add p q n
  map_smul' c p := by
    simp [SkewPolynomial.coeff, SkewMonoidAlgebra.coeff_smul]

theorem skew_coeff_sum {I : Type*} (s : Finset I) (p : I → SkewPolynomial K) (n : ℕ) :
    SkewPolynomial.coeff (∑ i ∈ s, p i) n = ∑ i ∈ s, SkewPolynomial.coeff (p i) n :=
  map_sum (skewCoeffLinear n) _ _

theorem skew_ext {p q : SkewPolynomial K}
    (h : ∀ n, SkewPolynomial.coeff p n = SkewPolynomial.coeff q n) : p = q := by
  apply SkewMonoidAlgebra.coeff_injective
  ext n
  exact h n.toAdd

def skewNatDegree (p : SkewPolynomial K) : ℕ := (SkewPolynomial.support p).sup id

theorem skew_support_le_degree (p : SkewPolynomial K) (i : ℕ)
    (hi : i ∈ SkewPolynomial.support p) : i ≤ skewNatDegree p := by
  exact Finset.le_sup (f := id) hi

theorem skew_coeff_above_degree (p : SkewPolynomial K) (i : ℕ) (hi : skewNatDegree p < i) :
    SkewPolynomial.coeff p i = 0 := by
  by_contra h
  exact (not_le_of_gt hi) (skew_support_le_degree p i (SkewPolynomial.mem_support_iff.mpr h))

theorem skew_leading_coefficient_nonzero (p : SkewPolynomial K) (hp : p ≠ 0) :
    SkewPolynomial.coeff p (skewNatDegree p) ≠ 0 := by
  have hs : (SkewPolynomial.support p).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    exact hp (SkewPolynomial.support_eq_empty.mp he)
  have hm := Finset.sup_mem_of_nonempty (f := id) hs
  have hm' : skewNatDegree p ∈ SkewPolynomial.support p := by
    simpa only [Set.image_id, Finset.mem_coe, skewNatDegree] using hm
  exact SkewPolynomial.mem_support_iff.mp hm'

variable [MulSemiringAction (Multiplicative ℕ) K]

theorem skew_coeff_mul_expansion (p q : SkewPolynomial K) (n : ℕ) :
    SkewPolynomial.coeff (p*q) n =
      ∑ i ∈ SkewPolynomial.support p, ∑ j ∈ SkewPolynomial.support q,
        if i+j=n then SkewPolynomial.coeff p i *
          (SkewPolynomial.φ^[i]) (SkewPolynomial.coeff q j) else 0 := by
  simp only [SkewPolynomial.mul_def, SkewPolynomial.sum_def, skew_coeff_sum,
    SkewPolynomial.coeff_monomial]

theorem skew_top_coefficient (p q : SkewPolynomial K) :
    SkewPolynomial.coeff (p*q) (skewNatDegree p + skewNatDegree q) =
      SkewPolynomial.coeff p (skewNatDegree p) *
        (SkewPolynomial.φ^[skewNatDegree p]) (SkewPolynomial.coeff q (skewNatDegree q)) := by
  classical
  rw [skew_coeff_mul_expansion, Finset.sum_eq_single (skewNatDegree p)]
  · rw [Finset.sum_eq_single (skewNatDegree q)]
    · simp
    · intro j hj hne
      simp [hne]
    · intro hj
      have hzero : SkewPolynomial.coeff q (skewNatDegree q) = 0 :=
        SkewPolynomial.notMem_support_iff.mp hj
      simp [hzero]
  · intro i hi hne
    apply Finset.sum_eq_zero
    intro j hj
    have hi' := skew_support_le_degree p i hi
    have hj' := skew_support_le_degree q j hj
    have hn : i+j ≠ skewNatDegree p+skewNatDegree q := by omega
    simp [hn]
  · intro hp
    have hzero : SkewPolynomial.coeff p (skewNatDegree p) = 0 :=
      SkewPolynomial.notMem_support_iff.mp hp
    simp [hzero]

theorem skew_phi_iterate_nonzero (a : K) (ha : a ≠ 0) (n : ℕ) :
    (SkewPolynomial.φ^[n]) a ≠ 0 := by
  have hi : Function.Injective (SkewPolynomial.φ : K → K) :=
    (SkewPolynomial.φ : K →+* K).injective
  intro h
  apply ha
  apply hi.iterate n
  simpa only [iterate_map_zero] using h

theorem skew_mul_nonzero (p q : SkewPolynomial K) (hp : p ≠ 0) (hq : q ≠ 0) : p*q ≠ 0 := by
  intro h
  have hc := congrArg (fun f : SkewPolynomial K =>
    SkewPolynomial.coeff f (skewNatDegree p+skewNatDegree q)) h
  rw [skew_top_coefficient, SkewPolynomial.coeff_zero] at hc
  exact (mul_ne_zero (skew_leading_coefficient_nonzero p hp)
    (skew_phi_iterate_nonzero _ (skew_leading_coefficient_nonzero q hq) _)) hc

instance skewPolynomial_noZeroDivisors : NoZeroDivisors (SkewPolynomial K) where
  eq_zero_or_eq_zero_of_mul_eq_zero {p q} h := by
    by_cases hp : p = 0
    · exact Or.inl hp
    · by_cases hq : q = 0
      · exact Or.inr hq
      · exact False.elim (skew_mul_nonzero p q hp hq h)

theorem skew_product_bounded (p q : SkewPolynomial K) (m n : ℕ)
    (hp : ∀ i, i ∈ SkewPolynomial.support p → i ≤ m)
    (hq : ∀ j, j ∈ SkewPolynomial.support q → j ≤ n) (k : ℕ) (hk : m+n < k) :
    SkewPolynomial.coeff (p*q) k = 0 := by
  rw [skew_coeff_mul_expansion]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  have hi' := hp i hi
  have hj' := hq j hj
  have hn : i+j ≠ k := by omega
  simp [hn]

end

end QuantumFlags

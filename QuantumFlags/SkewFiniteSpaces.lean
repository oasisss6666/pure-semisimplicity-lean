import QuantumFlags.SkewDomain
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.NoncommRing

namespace QuantumFlags

noncomputable section

variable {K : Type*} [DivisionRing K]

def boundedSkew (m : ℕ) : Submodule K (SkewPolynomial K) where
  carrier := {p | ∀ k, m < k → SkewPolynomial.coeff p k = 0}
  zero_mem' := by simp
  add_mem' hp hq k hk := by rw [SkewPolynomial.coeff_add, hp k hk, hq k hk, add_zero]
  smul_mem' c p hp k hk := by
    change skewCoeffLinear k (c • p) = 0
    rw [map_smul, show skewCoeffLinear k p = 0 from hp k hk, smul_zero]

def skewOfCoefficients (m : ℕ) (c : Fin (m+1) → K) : SkewPolynomial K :=
  ∑ i, SkewPolynomial.monomial i.val (c i)

theorem skewOfCoefficients_coeff_le (m : ℕ) (c : Fin (m+1) → K) (k : ℕ) (hk : k ≤ m) :
    SkewPolynomial.coeff (skewOfCoefficients m c) k = c ⟨k, Nat.lt_succ_of_le hk⟩ := by
  classical
  unfold skewOfCoefficients
  rw [skew_coeff_sum, Finset.sum_eq_single (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (m+1))]
  · simp [SkewPolynomial.coeff_monomial]
  · intro j _ hne
    have hn : j.val ≠ k := by
      intro h
      exact hne (Fin.ext h)
    simp [SkewPolynomial.coeff_monomial, hn]
  · simp

theorem skewOfCoefficients_coeff_above (m : ℕ) (c : Fin (m+1) → K) (k : ℕ) (hk : m < k) :
    SkewPolynomial.coeff (skewOfCoefficients m c) k = 0 := by
  unfold skewOfCoefficients
  rw [skew_coeff_sum]
  apply Finset.sum_eq_zero
  intro j _
  have hn : j.val ≠ k := by have hj := j.isLt; omega
  simp [SkewPolynomial.coeff_monomial, hn]

def boundedSkewEquiv (m : ℕ) : boundedSkew (K := K) m ≃ₗ[K] (Fin (m+1) → K) where
  toFun p i := SkewPolynomial.coeff (p : SkewPolynomial K) i.val
  invFun c := ⟨skewOfCoefficients m c, skewOfCoefficients_coeff_above m c⟩
  left_inv p := by
    apply Subtype.ext
    apply skew_ext
    intro k
    change SkewPolynomial.coeff
      (skewOfCoefficients m (fun i => SkewPolynomial.coeff (p : SkewPolynomial K) i.val)) k =
        SkewPolynomial.coeff (p : SkewPolynomial K) k
    by_cases hk : k ≤ m
    · rw [skewOfCoefficients_coeff_le m _ k hk]
    · rw [skewOfCoefficients_coeff_above m _ k (Nat.lt_of_not_ge hk),
        p.property k (Nat.lt_of_not_ge hk)]
  right_inv c := by
    funext i
    exact skewOfCoefficients_coeff_le m c i.val (Nat.le_of_lt_succ i.isLt)
  map_add' p q := by
    funext i
    exact SkewPolynomial.coeff_add (p : SkewPolynomial K) (q : SkewPolynomial K) i.val
  map_smul' c p := by
    funext i
    exact (skewCoeffLinear i.val).map_smul c (p : SkewPolynomial K)

instance boundedSkew_finiteDimensional (m : ℕ) : FiniteDimensional K (boundedSkew (K := K) m) :=
  FiniteDimensional.of_injective (boundedSkewEquiv m).toLinearMap (boundedSkewEquiv m).injective

theorem boundedSkew_finrank (m : ℕ) : Module.finrank K (boundedSkew (K := K) m) = m+1 := by
  simpa using (boundedSkewEquiv (K := K) m).finrank_eq

theorem boundedSkew_support (m : ℕ) (p : boundedSkew (K := K) m) (i : ℕ)
    (hi : i ∈ SkewPolynomial.support (p : SkewPolynomial K)) : i ≤ m := by
  by_contra h
  exact (SkewPolynomial.mem_support_iff.mp hi) (p.property i (Nat.lt_of_not_ge h))

variable [MulSemiringAction (Multiplicative ℕ) K]

theorem boundedSkew_product (m n : ℕ) (p : boundedSkew (K := K) m)
    (q : boundedSkew (K := K) n) :
    (p : SkewPolynomial K)*(q : SkewPolynomial K) ∈ boundedSkew (m+n) := by
  intro k hk
  exact skew_product_bounded _ _ m n (boundedSkew_support m p) (boundedSkew_support n q) k hk

def skewLeftRelation (m : ℕ) (p q : boundedSkew (K := K) m) :
    (boundedSkew (K := K) m × boundedSkew (K := K) m) →ₗ[K] boundedSkew (K := K) (m+m) where
  toFun w := ⟨(w.1 : SkewPolynomial K)*(p : SkewPolynomial K) -
      (w.2 : SkewPolynomial K)*(q : SkewPolynomial K),
    (boundedSkew (K := K) (m+m)).sub_mem (boundedSkew_product m m w.1 p) (boundedSkew_product m m w.2 q)⟩
  map_add' w z := by
    apply Subtype.ext
    change ((w.1 : SkewPolynomial K)+(z.1 : SkewPolynomial K))*(p : SkewPolynomial K) -
      ((w.2 : SkewPolynomial K)+(z.2 : SkewPolynomial K))*(q : SkewPolynomial K) =
      ((w.1 : SkewPolynomial K)*(p : SkewPolynomial K) -
        (w.2 : SkewPolynomial K)*(q : SkewPolynomial K)) +
      ((z.1 : SkewPolynomial K)*(p : SkewPolynomial K) -
        (z.2 : SkewPolynomial K)*(q : SkewPolynomial K))
    noncomm_ring
  map_smul' c w := by
    apply Subtype.ext
    change (c • (w.1 : SkewPolynomial K))*(p : SkewPolynomial K) -
      (c • (w.2 : SkewPolynomial K))*(q : SkewPolynomial K) =
        c • ((w.1 : SkewPolynomial K)*(p : SkewPolynomial K) -
          (w.2 : SkewPolynomial K)*(q : SkewPolynomial K))
    rw [smul_sub, smul_mul_assoc, smul_mul_assoc]

/-- The finite-dimensional kernel argument in Lemma 2.6, on the left.
No Ore condition or division ring of fractions is assumed. -/
theorem skew_common_left_multiple (p q : SkewPolynomial K) (hp : p ≠ 0) (hq : q ≠ 0) :
    ∃ X Y : SkewPolynomial K, X ≠ 0 ∧ Y ≠ 0 ∧ X*p=Y*q := by
  let m := max (skewNatDegree p) (skewNatDegree q)
  let p' : boundedSkew (K := K) m := ⟨p, fun k hk => skew_coeff_above_degree p k
    (lt_of_le_of_lt (le_max_left _ _) hk)⟩
  let q' : boundedSkew (K := K) m := ⟨q, fun k hk => skew_coeff_above_degree q k
    (lt_of_le_of_lt (le_max_right _ _) hk)⟩
  let f := skewLeftRelation m p' q'
  have hd : Module.finrank K (boundedSkew (K := K) (m+m)) <
      Module.finrank K (boundedSkew (K := K) m × boundedSkew (K := K) m) := by
    rw [Module.finrank_prod, boundedSkew_finrank, boundedSkew_finrank]
    omega
  have hker : LinearMap.ker f ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hd
  obtain ⟨w, hw, hwnz⟩ := (LinearMap.ker f).ne_bot_iff.mp hker
  have heq : (w.1 : SkewPolynomial K)*p = (w.2 : SkewPolynomial K)*q := by
    have he := congrArg (fun a : boundedSkew (K := K) (m+m) => (a : SkewPolynomial K))
      (LinearMap.mem_ker.mp hw)
    change (w.1 : SkewPolynomial K)*p - (w.2 : SkewPolynomial K)*q = 0 at he
    exact sub_eq_zero.mp he
  have hx : (w.1 : SkewPolynomial K) ≠ 0 := by
    intro h
    have hy : (w.2 : SkewPolynomial K) = 0 :=
      (mul_eq_zero.mp (by rw [← heq, h, zero_mul])).resolve_right hq
    exact hwnz (Prod.ext (Subtype.ext h) (Subtype.ext hy))
  have hy : (w.2 : SkewPolynomial K) ≠ 0 := by
    intro h
    have hx' : (w.1 : SkewPolynomial K) = 0 :=
      (mul_eq_zero.mp (by rw [heq, h, zero_mul])).resolve_right hp
    exact hx hx'
  exact ⟨w.1, w.2, hx, hy, heq⟩

end

end QuantumFlags

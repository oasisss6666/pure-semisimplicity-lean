import QuantumFlags.QuantumTower
import QuantumFlags.IntegerPowerIndependence

/-!
# Lemma `lem:qtorus`, first part

Manuscript `lem:qtorus` (source lines 175-190) for an arbitrary `q ∈ ℚ^×`:

* for `n ≥ 1` the automorphism `τ_n` of `T_n` is the unique ring endomorphism fixing `T_{n-1}`
  and sending `t_n` to `q t_n`;
* assertion (1): with `v = t_{n+1}`, `v a = τ_n(a) v` and `a v^h = v^h τ_n^{-h}(a)` for all
  `a ∈ T_n` and `h ∈ ℤ`, and distinct integer powers of `v` are linearly independent over `T_n`
  on both sides.
-/

namespace QuantumFlags
noncomputable section

variable (q : ℚ) (hq : q ≠ 0)

/-- `τ_n` (for `n = m+1`) is the only ring endomorphism of `T_n` fixing `T_{n-1}` and sending
`t_n` to `q t_n`. -/
theorem quantumAutomorphism_unique (m : ℕ)
    (σ : QuantumLevel q hq (m+1) →+* QuantumLevel q hq (m+1))
    (hfix : ∀ a, σ (quantumStep q hq m a) = quantumStep q hq m a)
    (hscale : σ (quantumGenerator q hq m) =
      ((q : ℚ) : QuantumLevel q hq (m+1)) * quantumGenerator q hq m) :
    σ = (quantumAutomorphism q hq (m+1)).toRingHom := by
  let K := QuantumLevel q hq m
  let τ := quantumAutomorphism q hq m
  letI := automorphismAction τ
  change (σ : SkewFractions K →+* SkewFractions K) =
    ((quantumAutomorphism q hq (m+1)).toRingHom : SkewFractions K →+* SkewFractions K)
  apply skew_fractionHom_ext
  intro p
  have h := skew_ringHom_ext (σ.comp skewNumerator)
    ((quantumAutomorphism q hq (m+1)).toRingHom.comp skewNumerator)
    (fun a => by
      change σ (quantumStep q hq m a) = quantumAutomorphism q hq (m+1) (quantumStep q hq m a)
      rw [hfix, quantumAutomorphism_fixes])
    (by
      change σ (quantumGenerator q hq m) =
        quantumAutomorphism q hq (m+1) (quantumGenerator q hq m)
      rw [hscale, quantumAutomorphism_scales])
  exact congrArg (fun φ => φ p) h

theorem quantumGenerator_ne_zero (n : ℕ) : quantumGenerator q hq n ≠ 0 :=
  extension_variable_ne_zero _

/-- Assertion (1), first relation: `v a = τ_n(a) v`. -/
theorem quantumGenerator_mul (n : ℕ) (a : QuantumLevel q hq n) :
    quantumGenerator q hq n * quantumStep q hq n a =
      quantumStep q hq n (quantumAutomorphism q hq n a) * quantumGenerator q hq n :=
  quantumGenerator_relation q hq n a

/-- `v^h a = τ_n^h(a) v^h` for natural `h`. -/
theorem quantumGenerator_pow_mul (n k : ℕ) (a : QuantumLevel q hq n) :
    quantumGenerator q hq n ^ k * quantumStep q hq n a =
      quantumStep q hq n (((quantumAutomorphism q hq n : RingAut _) ^ k) a) *
        quantumGenerator q hq n ^ k := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_assoc, quantumGenerator_mul, ← mul_assoc, ih, mul_assoc, pow_succ']
    congr 2
    rw [(Commute.self_pow (quantumAutomorphism q hq n : RingAut _) k).eq]
    rfl

/-- `v^h a = τ_n^h(a) v^h` for all integers `h`. -/
theorem quantumGenerator_zpow_mul (n : ℕ) (h : ℤ) (a : QuantumLevel q hq n) :
    quantumGenerator q hq n ^ h * quantumStep q hq n a =
      quantumStep q hq n (((quantumAutomorphism q hq n : RingAut _) ^ h) a) *
        quantumGenerator q hq n ^ h := by
  have hv := quantumGenerator_ne_zero q hq n
  rcases Int.eq_nat_or_neg h with ⟨k, rfl | rfl⟩
  · simp only [zpow_natCast]
    exact quantumGenerator_pow_mul q hq n k a
  · let σ := (quantumAutomorphism q hq n : RingAut _) ^ k
    have hk := quantumGenerator_pow_mul q hq n k (σ⁻¹ a)
    have hσ : ((quantumAutomorphism q hq n : RingAut _) ^ k) (σ⁻¹ a) = a := by
      change (σ * σ⁻¹) a = a
      rw [mul_inv_cancel]; rfl
    rw [hσ] at hk
    have hzinv : ((quantumAutomorphism q hq n : RingAut _) ^ (-(k : ℤ))) = σ⁻¹ := by
      rw [zpow_neg, zpow_natCast]
    rw [hzinv, zpow_neg, zpow_natCast]
    have hvk : quantumGenerator q hq n ^ k ≠ 0 := pow_ne_zero k hv
    calc (quantumGenerator q hq n ^ k)⁻¹ * quantumStep q hq n a
        = (quantumGenerator q hq n ^ k)⁻¹ *
            (quantumStep q hq n a * quantumGenerator q hq n ^ k) *
              (quantumGenerator q hq n ^ k)⁻¹ := by
          rw [mul_assoc, mul_assoc, mul_inv_cancel₀ hvk, mul_one]
      _ = (quantumGenerator q hq n ^ k)⁻¹ *
            (quantumGenerator q hq n ^ k * quantumStep q hq n (σ⁻¹ a)) *
              (quantumGenerator q hq n ^ k)⁻¹ := by rw [hk]
      _ = quantumStep q hq n (σ⁻¹ a) * (quantumGenerator q hq n ^ k)⁻¹ := by
          rw [← mul_assoc, inv_mul_cancel₀ hvk, one_mul]

/-- Assertion (1), second relation: `a v^h = v^h τ_n^{-h}(a)`. -/
theorem mul_quantumGenerator_zpow (n : ℕ) (h : ℤ) (a : QuantumLevel q hq n) :
    quantumStep q hq n a * quantumGenerator q hq n ^ h =
      quantumGenerator q hq n ^ h *
        quantumStep q hq n (((quantumAutomorphism q hq n : RingAut _) ^ (-h)) a) := by
  rw [quantumGenerator_zpow_mul]
  congr 2
  change a = (((quantumAutomorphism q hq n : RingAut _) ^ h) *
    ((quantumAutomorphism q hq n : RingAut _) ^ (-h))) a
  rw [← zpow_add, add_neg_cancel, zpow_zero]
  rfl

/-- Assertion (1): distinct integer powers of `t_{n+1}` are left linearly independent over
`T_n`. -/
theorem quantumGenerator_integer_left_powers_independent (n : ℕ) :
    letI := powerLeftCoefficientModule (quantumStep q hq n)
    LinearIndependent (QuantumLevel q hq n) (fun i : ℤ => quantumGenerator q hq n ^ i) :=
  extension_integer_left_powers_independent _

/-- Assertion (1): distinct integer powers of `t_{n+1}` are right linearly independent over
`T_n`. -/
theorem quantumGenerator_integer_right_powers_independent (n : ℕ) :
    letI := powerRightCoefficientModule (quantumStep q hq n)
    LinearIndependent (QuantumLevel q hq n)ᵐᵒᵖ (fun i : ℤ => quantumGenerator q hq n ^ i) :=
  extension_integer_right_powers_independent _

end
end QuantumFlags

import QuantumFlags.AutomorphismRecurrence

namespace QuantumFlags

variable {K D : Type*} [DivisionRing K] [DivisionRing D] [CharZero K] [CharZero D]

theorem wideVandermonde_apply (n : ℕ) (k h : Fin n) :
    wideVandermonde (D := D) n k h = (((((2 : ℚ)^k.val)^h.val : ℚ) : D)) := rfl

omit [CharZero K] [CharZero D] in
theorem scaled_normalizes (ι : K →+* D) (v : D) (τ : K ≃+* K)
    (hτ : ∀ a, v*ι a = ι (τ a)*v) (s : ℚ) (a : K) :
    ((s : D)*v)*ι a = ι (τ a)*((s : D)*v) := by
  rw [mul_assoc, hτ, ← mul_assoc, (Rat.cast_commute s (ι (τ a))).eq, mul_assoc]

omit [CharZero K] in
theorem actual_coordinate_matrix_step (ι : K →+* D) (v : D) (τ : K ≃+* K)
    (hτ : ∀ a, v*ι a = ι (τ a)*v) (ρ : D ≃+* D)
    (a : K) (hfix : ρ (ι a) = ι a) (hscale : ρ v = half D*v)
    (hv : NotRational v) (r : ℕ) :
    wideDenominator r v * automorphismCoordinates ρ
        ((poch (half D) r v)⁻¹*ι a*poch (half D) r v) r =
      wideVandermonde (r+1) *
        wideCoefficientDiagonal r (fun h => (quantumPoly r).coeff h.val) v *
          (automorphismCoordinates τ a r).map ι := by
  ext k i
  rw [wideDenominator, Matrix.diagonal_mul]
  change poch (half D) r (((((2 : ℚ)^k.val : ℚ) : D))*v) *
      (ρ.symm^[k.val]) (((poch (half D) r v)⁻¹*ι a*poch (half D) r v)^i.val) = _
  rw [automorphism_conjugate_coordinates ρ (ι a) v hfix hscale hv]
  have hP : poch (half D) r (((((2 : ℚ)^k.val : ℚ) : D))*v) ≠ 0 :=
    poch_ne_zero _ (rat_mul_notRational v hv _ (pow_ne_zero _ (by norm_num))) (1/2) r
  rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hP, one_mul, ← map_pow]
  rw [skew_poch_expansion ι _ τ (scaled_normalizes ι v τ hτ _) (a^i.val) r,
    ← Fin.sum_univ_eq_sum_range, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro h _
  rw [(Rat.cast_commute ((2 : ℚ)^k.val) v).mul_pow]
  simp only [wideCoefficientDiagonal, Matrix.mul_diagonal, wideVandermonde_apply,
    Matrix.map_apply, automorphismCoordinates]
  have hcast : (((((2 : ℚ)^k.val)^h.val : ℚ) : D)) =
      (((((2 : ℚ)^k.val : ℚ) : D)))^h.val :=
    map_pow (Rat.castHom D) _ _
  rw [hcast]
  noncomm_ring [(Rat.cast_commute ((quantumPoly r).coeff h.val) (v^h.val)).eq]

theorem actual_coordinate_step_hasInverse (ι : K →+* D) (v : D) (τ : K ≃+* K)
    (hτ : ∀ a, v*ι a = ι (τ a)*v) (ρ : D ≃+* D)
    (a : K) (hfix : ρ (ι a) = ι a) (hscale : ρ v = half D*v)
    (hv : NotRational v) (r : ℕ)
    (hA : FullInverse (automorphismCoordinates τ a r)) :
    FullInverse (automorphismCoordinates ρ
      ((poch (half D) r v)⁻¹*ι a*poch (half D) r v) r) := by
  have he := actual_coordinate_matrix_step ι v τ hτ ρ a hfix hscale hv r
  have hh := congrArg (fun M => wideDenominatorInv r v*M) he
  have hsol : automorphismCoordinates ρ
      ((poch (half D) r v)⁻¹*ι a*poch (half D) r v) r =
      wideDenominatorInv r v * wideVandermonde (r+1) *
        wideCoefficientDiagonal r (fun h => (quantumPoly r).coeff h.val) v *
          (automorphismCoordinates τ a r).map ι := by
    simpa only [← mul_assoc, (wideDenominator_cancels r v hv).2, one_mul] using hh
  rw [hsol]
  exact (((wideDenominatorInv_hasInverse r v hv).mul (wideVandermonde_hasInverse _)).mul
    (wideCoefficientDiagonal_hasInverse r _
      (fun h => quantumPoly_coeff_nonzero r h.val (Nat.le_of_lt_succ h.isLt)) v
        (notRational_ne_zero hv))).mul (hA.map ι)

end QuantumFlags

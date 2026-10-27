import QuantumFlags.Coefficients

namespace QuantumFlags

variable {K D : Type*} [DivisionRing K] [DivisionRing D]

theorem skew_move_right (ι : K →+* D) (v : D) (τ : K ≃+* K)
    (hτ : ∀ a, v*ι a = ι (τ a)*v) (a : K) :
    ι a*v = v*ι (τ.symm a) := by
  simpa only [RingEquiv.apply_symm_apply] using (hτ (τ.symm a)).symm

theorem skew_move_power (ι : K →+* D) (v : D) (τ : K ≃+* K)
    (hτ : ∀ a, v*ι a = ι (τ a)*v) (a : K) (h : ℕ) :
    ι a*v^h = v^h*ι ((τ.symm^[h]) a) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [pow_succ, ← mul_assoc, ih, mul_assoc, skew_move_right ι v τ hτ,
      ← mul_assoc, ← pow_succ, Function.iterate_succ_apply']

variable [CharZero D]

/-- Coefficient movement uses the inverse automorphism. The order of all
noncentral coefficients is retained. -/
theorem skew_poch_expansion (ι : K →+* D) (v : D) (τ : K ≃+* K)
    (hτ : ∀ a, v*ι a = ι (τ a)*v) (a : K) (r : ℕ) :
    ι a * poch (half D) r v =
      ∑ h ∈ Finset.range (r+1), v^h *
        (((quantumPoly r).coeff h : ℚ) : D) * ι ((τ.symm^[h]) a) := by
  rw [poch_coefficient_expansion, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  calc
    ι a * ((((quantumPoly r).coeff h : ℚ) : D)*v^h) =
        (((quantumPoly r).coeff h : ℚ) : D)*(ι a*v^h) :=
      (Rat.cast_commute _ (ι a)).symm.left_comm (v^h)
    _ = (((quantumPoly r).coeff h : ℚ) : D)*(v^h*ι ((τ.symm^[h]) a)) := by
      rw [skew_move_power ι v τ hτ]
    _ = _ := by rw [(Rat.cast_commute _ (v^h)).left_comm, ← mul_assoc]

omit [CharZero D] in
theorem inverse_conjugate_pow (P a : D) (hP : P ≠ 0) (i : ℕ) :
    (P⁻¹*a*P)^i = P⁻¹*a^i*P := by
  have hh := (innerHom (P⁻¹) (inv_ne_zero hP)).map_pow a i
  simpa only [innerHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, inv_inv]
    using hh.symm

/-- Equation (zpowers), for the actual Pochhammer coefficients. -/
theorem conjugated_power_expansion (ι : K →+* D) (v : D) (τ : K ≃+* K)
    (hτ : ∀ a, v*ι a = ι (τ a)*v) (a : K) (r i : ℕ)
    (hv : NotRational v) :
    ((poch (half D) r v)⁻¹*ι a*poch (half D) r v)^i =
      ∑ h ∈ Finset.range (r+1), (poch (half D) r v)⁻¹*v^h *
        (((quantumPoly r).coeff h : ℚ) : D) * ι ((τ.symm^[h]) (a^i)) := by
  have hP : poch (half D) r v ≠ 0 := poch_ne_zero v hv (1/2) r
  rw [inverse_conjugate_pow _ _ hP, ← map_pow,
    mul_assoc, skew_poch_expansion ι v τ hτ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  simp only [mul_assoc]

end QuantumFlags

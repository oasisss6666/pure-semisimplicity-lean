import QuantumFlags.WideBasis

namespace QuantumFlags

variable {K D : Type*} [DivisionRing K] [DivisionRing D]

def inverseIterateHom (τ : D ≃+* D) : ℕ → D →+* D
  | 0 => RingHom.id D
  | k+1 => τ.symm.toRingHom.comp (inverseIterateHom τ k)

theorem inverseIterateHom_apply (τ : D ≃+* D) (k : ℕ) (a : D) :
    inverseIterateHom τ k a = (τ.symm^[k]) a := by
  induction k with
  | zero => rfl
  | succ k ih => simp [inverseIterateHom, ih, Function.iterate_succ_apply']

theorem poch_map (ι : K →+* D) (q v : K) (r : ℕ) :
    ι (poch q r v) = poch (ι q) r (ι v) := by
  induction r with
  | zero => exact map_one _
  | succ r ih => simp only [poch, map_mul, map_sub, map_one, map_pow, ih]

theorem inverseIterateHom_fixed (τ : D ≃+* D) (a : D) (h : τ a = a) (k : ℕ) :
    inverseIterateHom τ k a = a := by
  have hs : τ.symm a = a := by
    apply τ.injective
    simpa only [RingEquiv.apply_symm_apply] using h.symm
  induction k with
  | zero => rfl
  | succ k ih => simp only [inverseIterateHom, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe, ih, hs]

variable [CharZero D]

theorem inverse_scales_by_two (τ : D ≃+* D) (v : D) (h : τ v = half D*v) :
    τ.symm v = (2 : D)*v := by
  have htwo : (2 : D)*half D=1 := by norm_num [half]
  apply τ.injective
  simp only [RingEquiv.apply_symm_apply, map_mul, map_ofNat, h, ← mul_assoc,
    htwo, one_mul]

theorem inverseIterateHom_scaled (τ : D ≃+* D) (v : D)
    (h : τ v = half D*v) (k : ℕ) :
    inverseIterateHom τ k v = ((((2 : ℚ)^k : ℚ) : D))*v := by
  induction k with
  | zero => simp [inverseIterateHom]
  | succ k ih =>
    simp only [inverseIterateHom, RingHom.comp_apply, ih, map_mul, map_ratCast,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      inverse_scales_by_two τ v h, pow_succ, Rat.cast_mul, Rat.cast_ofNat, mul_assoc]

theorem inverseIterateHom_poch (τ : D ≃+* D) (v : D)
    (h : τ v = half D*v) (k r : ℕ) :
    inverseIterateHom τ k (poch (half D) r v) =
      poch (half D) r (((((2 : ℚ)^k : ℚ) : D))*v) := by
  rw [poch_map, inverseIterateHom_scaled τ v h]
  congr 1
  exact map_ratCast _ _

theorem automorphism_conjugate_coordinates (ρ : D ≃+* D) (u v : D)
    (hfix : ρ u = u) (hscale : ρ v = half D*v) (hv : NotRational v) (r k i : ℕ) :
    (ρ.symm^[k]) (((poch (half D) r v)⁻¹*u*poch (half D) r v)^i) =
      (poch (half D) r (((((2 : ℚ)^k : ℚ) : D))*v))⁻¹ * u^i *
        poch (half D) r (((((2 : ℚ)^k : ℚ) : D))*v) := by
  rw [← inverseIterateHom_apply, map_pow, map_mul, map_mul, map_inv₀,
    inverseIterateHom_poch ρ v hscale, inverseIterateHom_fixed ρ u hfix]
  have hP : poch (half D) r (((((2 : ℚ)^k : ℚ) : D))*v) ≠ 0 :=
    poch_ne_zero _ (rat_mul_notRational v hv _ (pow_ne_zero _ (by norm_num))) (1/2) r
  exact inverse_conjugate_pow _ _ hP i

end QuantumFlags

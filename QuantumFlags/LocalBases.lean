import QuantumFlags.PowerChain

namespace QuantumFlags

variable {D : Type*} [DivisionRing D] [CharZero D]

theorem chainU_succ_coe (Q : QuantumChain D) (p n : ℕ) :
    (chainU Q p (n+1) : D) =
      (poch (half D) p (Q.x (n+1)))⁻¹ * (chainU Q p n : D) *
        poch (half D) p (Q.x (n+1)) := by
  have he := congrArg (Q.layer (n+2)).subtype (chainU_succ Q p n)
  have hi (a : Q.layer (n+1)) :
      ((layerInclusion Q (n+1) a : Q.layer (n+2)) : D) = (a : D) := rfl
  simpa only [map_mul, map_inv₀, poch_map, Subfield.subtype_apply, hi,
    half, SubfieldClass.coe_ratCast, chainGenerator] using he

theorem chain_local_power_basis (Q : QuantumChain D) (B : PowerChainProperties Q)
    (r n : ℕ) :
    Function.Injective (wideEval (Q.layer (n+1)).subtype
      (fun i : Fin (r+1) => (chainU Q r (n+1) : D)^i.val)) ∧
    Set.range (wideEval (Q.layer (n+1)).subtype
      (fun i : Fin (r+1) => (chainU Q r (n+1) : D)^i.val)) =
      Set.range (wideEval (Q.layer (n+1)).subtype
        (fun h : Fin (r+1) => (poch (half D) r (Q.x (n+1)))⁻¹*(Q.x (n+1))^h.val)) := by
  simp only [chainU_succ_coe]
  exact local_right_power_basis (Q.layer (n+1)).subtype (Q.x (n+1))
    (Q.normalizer (n+1)) (Q.normalizes (n+1)) (chainU Q r n) r
    (Q.not_rational (n+1)) (B.right_powers_independent (n+1) r)
    (chainU_coordinate_hasInverse Q B r n)

variable {K : Type*} [DivisionRing K] [CharZero K]

omit [CharZero K] in
theorem normalized_conjugate_in_strip (ι : K →+* D) (v : D) (τ : K ≃+* K)
    (hτ : ∀ a, v*ι a = ι (τ a)*v) (a : K) (r : ℕ) (hv : NotRational v) :
    (poch (half D) r v)⁻¹*ι a*poch (half D) r v ∈
      Set.range (wideEval ι
        (fun h : Fin (r+1) => (poch (half D) r v)⁻¹*v^h.val)) := by
  refine ⟨fun h => (((quantumPoly r).coeff h.val : ℚ) : K)*((τ.symm^[h.val]) a), ?_⟩
  have he := conjugated_power_expansion ι v τ hτ a r 1 hv
  rw [pow_one] at he
  rw [← Fin.sum_univ_eq_sum_range] at he
  rw [he]
  unfold wideEval
  apply Finset.sum_congr rfl
  intro h _
  simp only [map_mul, map_ratCast, pow_one, mul_assoc]

end QuantumFlags

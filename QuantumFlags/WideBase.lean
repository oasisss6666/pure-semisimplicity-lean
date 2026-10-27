import QuantumFlags.WideStep

namespace QuantumFlags

variable {D : Type*} [DivisionRing D] [CharZero D]

theorem inverseIterate_scaled_power (τ : D ≃+* D) (v : D)
    (h : τ v = half D*v) (k i : ℕ) :
    (τ.symm^[k]) (v^i) = (((((2 : ℚ)^k)^i : ℚ) : D))*v^i := by
  rw [← inverseIterateHom_apply, map_pow, inverseIterateHom_scaled τ v h k,
    (Rat.cast_commute ((2 : ℚ)^k) v).mul_pow]
  have hc : (((((2 : ℚ)^k)^i : ℚ) : D)) = (((((2 : ℚ)^k : ℚ) : D)))^i :=
    map_pow (Rat.castHom D) _ _
  rw [hc]

theorem actual_coordinate_matrix_base (τ : D ≃+* D) (v : D)
    (h : τ v = half D*v) (r : ℕ) :
    automorphismCoordinates τ v r =
      wideVandermonde (r+1) * Matrix.diagonal (fun i : Fin (r+1) => v^i.val) := by
  ext k i
  rw [Matrix.mul_diagonal, wideVandermonde_apply]
  exact inverseIterate_scaled_power τ v h k.val i.val

theorem actual_coordinate_base_hasInverse (τ : D ≃+* D) (v : D)
    (h : τ v = half D*v) (hv : v ≠ 0) (r : ℕ) :
    FullInverse (automorphismCoordinates τ v r) := by
  rw [actual_coordinate_matrix_base τ v h r]
  exact (wideVandermonde_hasInverse (D := D) _).mul
    (fullInverse_diagonal _ (fun i => pow_ne_zero i.val hv))

end QuantumFlags

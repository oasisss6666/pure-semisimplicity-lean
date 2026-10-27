import QuantumFlags.SkewExpansion

namespace QuantumFlags

variable {K D I : Type*} [DivisionRing K] [DivisionRing D] [Fintype I] [DecidableEq I]

def wideEval (ι : K →+* D) (w : I → D) (c : I → K) : D :=
  ∑ i, w i*ι (c i)

def wideFamilyEval (ι : K →+* D) (w : I → D) (M : Matrix I I K) (c : I → K) : D :=
  ∑ j, (∑ i, w i*ι (M i j))*ι (c j)

omit [DecidableEq I] in
theorem wide_change_coordinates (ι : K →+* D) (w : I → D) (M : Matrix I I K)
    (c : I → K) : wideFamilyEval ι w M c = wideEval ι w (M.mulVec c) := by
  simp only [wideFamilyEval, wideEval, Matrix.mulVec, dotProduct, map_sum, map_mul,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

theorem wide_basis_transport (ι : K →+* D) (w : I → D)
    (hbase : Function.Injective (wideEval ι w))
    (M : Matrix I I K) (hM : FullInverse M) :
    Function.Injective (wideFamilyEval ι w M) ∧
      Set.range (wideFamilyEval ι w M) = Set.range (wideEval ι w) := by
  constructor
  · intro c d h
    apply hM.mulVec_bijective.injective
    apply hbase
    simpa only [wide_change_coordinates] using h
  · ext z
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨M.mulVec c, (wide_change_coordinates ι w M c).symm⟩
    · rintro ⟨c, rfl⟩
      obtain ⟨d, hd⟩ := hM.mulVec_bijective.surjective c
      exact ⟨d, by rw [wide_change_coordinates, hd]⟩

variable [CharZero K] [CharZero D]

noncomputable def actualWideRecursion (r : ℕ) (x : ℕ → D) (n : ℕ) :
    Matrix (Fin (r+1)) (Fin (r+1)) D :=
  wideRecursion r (fun h => (quantumPoly r).coeff h.val) x n

theorem actualWideRecursion_hasInverse (r : ℕ) (x : ℕ → D)
    (hx : ∀ n, NotRational (x n)) (n : ℕ) :
    FullInverse (actualWideRecursion r x n) := by
  exact wideRecursion_hasInverse r _
    (fun h => quantumPoly_coeff_nonzero r h.val (Nat.le_of_lt_succ h.isLt)) x hx n

def automorphismCoordinates (τ : K ≃+* K) (a : K) (r : ℕ) :
    Matrix (Fin (r+1)) (Fin (r+1)) K :=
  fun h i => (τ.symm^[h.val]) (a^i.val)

noncomputable def weightedAutomorphismCoordinates (τ : K ≃+* K) (a : K) (r : ℕ) :
    Matrix (Fin (r+1)) (Fin (r+1)) K :=
  Matrix.diagonal (fun h : Fin (r+1) => (((quantumPoly r).coeff h.val : ℚ) : K)) *
    automorphismCoordinates τ a r

theorem weightedAutomorphismCoordinates_hasInverse (τ : K ≃+* K) (a : K) (r : ℕ)
    (hA : FullInverse (automorphismCoordinates τ a r)) :
    FullInverse (weightedAutomorphismCoordinates τ a r) := by
  apply FullInverse.mul _ hA
  apply fullInverse_diagonal
  intro h
  exact_mod_cast quantumPoly_coeff_nonzero r h.val (Nat.le_of_lt_succ h.isLt)

omit [CharZero K] in
theorem conjugated_power_coordinates (ι : K →+* D) (v : D) (τ : K ≃+* K)
    (hτ : ∀ a, v*ι a = ι (τ a)*v) (a : K) (r : ℕ) (i : Fin (r+1))
    (hv : NotRational v) :
    ((poch (half D) r v)⁻¹*ι a*poch (half D) r v)^i.val =
      ∑ h : Fin (r+1), (poch (half D) r v)⁻¹*v^h.val *
        ι (weightedAutomorphismCoordinates τ a r h i) := by
  rw [conjugated_power_expansion ι v τ hτ a r i.val hv]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro h _
  simp only [weightedAutomorphismCoordinates, Matrix.diagonal_mul,
    automorphismCoordinates, map_mul, map_ratCast, mul_assoc]

/-- If the actual automorphism-coordinate matrix is invertible, its conjugated
powers form a right basis of the local Pochhammer strip. The remaining task
for (B) is to establish this invertibility in the concrete chain via (Arec). -/
theorem local_right_power_basis (ι : K →+* D) (v : D) (τ : K ≃+* K)
    (hτ : ∀ a, v*ι a = ι (τ a)*v) (a : K) (r : ℕ) (hv : NotRational v)
    (hPBW : Function.Injective (wideEval ι (fun h : Fin (r+1) => v^h.val)))
    (hA : FullInverse (automorphismCoordinates τ a r)) :
    Function.Injective (wideEval ι (fun i : Fin (r+1) =>
      ((poch (half D) r v)⁻¹*ι a*poch (half D) r v)^i.val)) ∧
    Set.range (wideEval ι (fun i : Fin (r+1) =>
      ((poch (half D) r v)⁻¹*ι a*poch (half D) r v)^i.val)) =
      Set.range (wideEval ι (fun h : Fin (r+1) => (poch (half D) r v)⁻¹*v^h.val)) := by
  have hP : poch (half D) r v ≠ 0 := poch_ne_zero v hv (1/2) r
  have hbase : Function.Injective
      (wideEval ι (fun h : Fin (r+1) => (poch (half D) r v)⁻¹*v^h.val)) := by
    intro c d h
    apply hPBW
    apply mul_left_cancel₀ (inv_ne_zero hP)
    simpa only [wideEval, Finset.mul_sum, mul_assoc] using h
  have he : wideEval ι (fun i : Fin (r+1) =>
      ((poch (half D) r v)⁻¹*ι a*poch (half D) r v)^i.val) =
      wideFamilyEval ι (fun h : Fin (r+1) => (poch (half D) r v)⁻¹*v^h.val)
        (weightedAutomorphismCoordinates τ a r) := by
    funext c
    simp only [wideEval, wideFamilyEval, conjugated_power_coordinates ι v τ hτ a r _ hv]
  rw [he]
  exact wide_basis_transport ι _ hbase _ (weightedAutomorphismCoordinates_hasInverse τ a r hA)

end QuantumFlags

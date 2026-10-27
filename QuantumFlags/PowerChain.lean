import QuantumFlags.WideBase

namespace QuantumFlags

variable {D : Type*} [DivisionRing D] [CharZero D]

def layerInclusion (Q : QuantumChain D) (n : ℕ) : Q.layer n →+* Q.layer (n+1) :=
  Subfield.inclusion (Q.increasing (Nat.le_succ n))

def chainGenerator (Q : QuantumChain D) (n : ℕ) : Q.layer (n+1) :=
  ⟨Q.x n, Q.generator_mem n⟩

/-- Further basic Ore/PBW properties used for right bases of arbitrary width.
No invertibility of the desired coordinate matrix is assumed here. -/
structure PowerChainProperties (Q : QuantumChain D) : Prop where
  fixes_previous : ∀ n (a : Q.layer n),
    Q.normalizer (n+1) (layerInclusion Q n a) = layerInclusion Q n a
  scales_previous : ∀ n, Q.normalizer (n+1) (chainGenerator Q n) =
    half (Q.layer (n+1))*chainGenerator Q n
  right_powers_independent : ∀ n r,
    Function.Injective (wideEval (Q.layer n).subtype (fun h : Fin (r+1) => (Q.x n)^h.val))

omit [CharZero D] in
theorem poch_mem (L : Subfield D) (q v : D) (hq : q ∈ L) (hv : v ∈ L) (r : ℕ) :
    poch q r v ∈ L := by
  induction r with
  | zero => exact L.one_mem
  | succ r ih => exact L.mul_mem ih (L.sub_mem L.one_mem (L.mul_mem (L.pow_mem hq r) hv))

theorem gamma_mem (Q : QuantumChain D) (p n : ℕ) : gamma Q.x p n ∈ Q.layer (n+1) := by
  induction n with
  | zero => exact (Q.layer 1).sub_mem (Q.layer 1).one_mem (Q.generator_mem 0)
  | succ n ih =>
    exact (Q.layer (n+2)).mul_mem (Q.increasing (Nat.le_succ (n+1)) ih)
      (poch_mem _ _ _ (SubfieldClass.ratCast_mem _ _) (Q.generator_mem (n+1)) p)

def gammaInLayer (Q : QuantumChain D) (p n : ℕ) : Q.layer (n+1) :=
  ⟨gamma Q.x p n, gamma_mem Q p n⟩

def firstInLayer (Q : QuantumChain D) (n : ℕ) : Q.layer (n+1) :=
  ⟨Q.x 0, Q.increasing (Nat.succ_le_succ (Nat.zero_le n)) (Q.generator_mem 0)⟩

def chainU (Q : QuantumChain D) (p n : ℕ) : Q.layer (n+1) :=
  (gammaInLayer Q p n)⁻¹ * firstInLayer Q n * gammaInLayer Q p n

theorem chainU_zero (Q : QuantumChain D) (p : ℕ) : chainU Q p 0 = chainGenerator Q 0 := by
  apply Subtype.ext
  change (1-Q.x 0)⁻¹*Q.x 0*(1-Q.x 0) = Q.x 0
  have h : 1-Q.x 0 ≠ 0 := by
    simpa using linear_factor_ne_zero (Q.x 0) (Q.not_rational 0) 1
  have hc : Commute (1-Q.x 0) (Q.x 0) :=
    (Commute.one_left _).sub_left (Commute.refl _)
  rw [hc.inv_left₀.eq, mul_assoc, inv_mul_cancel₀ h, mul_one]

theorem chainU_succ (Q : QuantumChain D) (p n : ℕ) :
    chainU Q p (n+1) =
      (poch (half (Q.layer (n+2))) p (chainGenerator Q (n+1)))⁻¹ *
        layerInclusion Q (n+1) (chainU Q p n) *
          poch (half (Q.layer (n+2))) p (chainGenerator Q (n+1)) := by
  apply Subtype.ext
  change (gamma Q.x p (n+1))⁻¹*Q.x 0*gamma Q.x p (n+1) = _
  have hp : ((poch (half (Q.layer (n+2))) p (chainGenerator Q (n+1)) : Q.layer (n+2)) : D) =
      poch (half D) p (Q.x (n+1)) := by
    have he := poch_map (Q.layer (n+2)).subtype
      (half (Q.layer (n+2))) (chainGenerator Q (n+1)) p
    exact he
  change (gamma Q.x p (n+1))⁻¹*Q.x 0*gamma Q.x p (n+1) =
    (((poch (half (Q.layer (n+2))) p (chainGenerator Q (n+1)) : Q.layer (n+2)) : D))⁻¹ *
      ((gamma Q.x p n)⁻¹*Q.x 0*gamma Q.x p n) *
        ((poch (half (Q.layer (n+2))) p (chainGenerator Q (n+1)) : Q.layer (n+2)) : D)
  rw [hp]
  simp only [gamma, mul_inv_rev, mul_assoc]

theorem layer_normalizes_generator (Q : QuantumChain D) (n : ℕ) (a : Q.layer (n+1)) :
    chainGenerator Q (n+1) * layerInclusion Q (n+1) a =
      layerInclusion Q (n+1) (Q.normalizer (n+1) a) * chainGenerator Q (n+1) := by
  apply Subtype.ext
  exact Q.normalizes (n+1) a

theorem chainU_coordinate_hasInverse (Q : QuantumChain D) (B : PowerChainProperties Q)
    (r n : ℕ) : FullInverse (automorphismCoordinates (Q.normalizer (n+1)) (chainU Q r n) r) := by
  induction n with
  | zero =>
    rw [chainU_zero]
    exact actual_coordinate_base_hasInverse _ _ (B.scales_previous 0)
      (by
        intro h
        have hh := congrArg (fun a : Q.layer 1 => (a : D)) h
        exact notRational_ne_zero (Q.not_rational 0) hh) r
  | succ n ih =>
    rw [chainU_succ]
    apply actual_coordinate_step_hasInverse (layerInclusion Q (n+1))
      (chainGenerator Q (n+1)) (Q.normalizer (n+1)) (layer_normalizes_generator Q n)
      (Q.normalizer (n+2)) (chainU Q r n) (B.fixes_previous (n+1) _)
      (B.scales_previous (n+1))
    · intro s h
      have hh := congrArg (fun a : Q.layer (n+2) => (a : D)) h
      exact Q.not_rational (n+1) s hh
    · exact ih

end QuantumFlags

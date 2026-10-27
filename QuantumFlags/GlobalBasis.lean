import QuantumFlags.LocalBases

namespace QuantumFlags

noncomputable section

variable {D : Type*} [DivisionRing D] [CharZero D]

theorem finite_family_layer {I : Type*} [Fintype I] (Q : QuantumChain D) (c : I → D) :
    ∃ n, ∀ i, c i ∈ Q.layer n := by
  classical
  choose f hf using fun i => Q.covers (c i)
  refine ⟨Finset.univ.sup f, ?_⟩
  intro i
  exact Q.increasing (Finset.le_sup (Finset.mem_univ i)) (hf i)

def inverseInnerHom (g : D) (hg : g ≠ 0) : D →+* D where
  toFun a := g⁻¹*a*g
  map_zero' := by simp
  map_one' := by simp [hg]
  map_add' a b := by noncomm_ring
  map_mul' a b := by simp only [mul_assoc, mul_inv_cancel_left₀ hg]

def globalPowerEval (Q : QuantumChain D) (r : ℕ) (c : Fin (r+1) → D) : D :=
  ∑ i, (Q.x 0)^i.val*kappa Q r (c i)

theorem globalPowerEval_normalization (Q : QuantumChain D) (r n : ℕ)
    (c : Fin (r+1) → Q.layer n) :
    (gamma Q.x r n)⁻¹ * globalPowerEval Q r (fun i => (c i : D))*gamma Q.x r n =
      wideEval (Q.layer n).subtype (fun i : Fin (r+1) => (chainU Q r n : D)^i.val) c := by
  let f := inverseInnerHom (gamma Q.x r n)
    (gamma_ne_zero Q.x Q.not_rational r n)
  change f (globalPowerEval Q r (fun i => (c i : D))) = _
  unfold globalPowerEval wideEval
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, map_pow]
  have hc : f (kappa Q r (c i)) = (c i : D) := by
    rw [kappa_at Q r n _ (c i).property]
    change (gamma Q.x r n)⁻¹ * (gamma Q.x r n*(c i : D)*(gamma Q.x r n)⁻¹) *
      gamma Q.x r n = (c i : D)
    simp only [inv_inv, mul_assoc,
      inv_mul_cancel_left₀ (gamma_ne_zero Q.x Q.not_rational r n)]
    rw [inv_mul_cancel₀ (gamma_ne_zero Q.x Q.not_rational r n), mul_one]
  rw [hc]
  rfl

theorem normalized_element_in_strip (Q : QuantumChain D) (r n : ℕ)
    (a : Q.layer (n+1)) :
    (gamma Q.x r (n+1))⁻¹*(a : D)*gamma Q.x r (n+1) ∈
      Set.range (wideEval (Q.layer (n+1)).subtype
        (fun h : Fin (r+1) =>
          (poch (half D) r (Q.x (n+1)))⁻¹*(Q.x (n+1))^h.val)) := by
  let a' := (gammaInLayer Q r n)⁻¹*a*gammaInLayer Q r n
  have he := normalized_conjugate_in_strip (Q.layer (n+1)).subtype (Q.x (n+1))
    (Q.normalizer (n+1)) (Q.normalizes (n+1)) a' r (Q.not_rational (n+1))
  have ha : ((gamma Q.x r (n+1))⁻¹*(a : D)*gamma Q.x r (n+1)) =
      (poch (half D) r (Q.x (n+1)))⁻¹ * (a' : D) *
        poch (half D) r (Q.x (n+1)) := by
    change (gamma Q.x r (n+1))⁻¹*(a : D)*gamma Q.x r (n+1) =
      (poch (half D) r (Q.x (n+1)))⁻¹ *
        ((gamma Q.x r n)⁻¹*(a : D)*gamma Q.x r n) *
          poch (half D) r (Q.x (n+1))
    simp only [gamma, mul_inv_rev, mul_assoc]
  rw [ha]
  exact he

theorem globalPowerEval_injective (Q : QuantumChain D) (B : PowerChainProperties Q) (r : ℕ) :
    Function.Injective (globalPowerEval Q r) := by
  intro c d h
  obtain ⟨n, hn⟩ := finite_family_layer Q c
  obtain ⟨m, hm⟩ := finite_family_layer Q d
  let N := max n m
  let c' : Fin (r+1) → Q.layer (N+1) := fun i =>
    ⟨c i, Q.increasing (le_trans (le_max_left _ _) (Nat.le_succ N)) (hn i)⟩
  let d' : Fin (r+1) → Q.layer (N+1) := fun i =>
    ⟨d i, Q.increasing (le_trans (le_max_right _ _) (Nat.le_succ N)) (hm i)⟩
  have he : c' = d' := (chain_local_power_basis Q B r N).1 (by
    rw [← globalPowerEval_normalization Q r (N+1) c',
      ← globalPowerEval_normalization Q r (N+1) d']
    exact congrArg (fun z => (gamma Q.x r (N+1))⁻¹*z*gamma Q.x r (N+1)) h)
  funext i
  exact congrArg (fun a : Q.layer (N+1) => (a : D)) (congrFun he i)

theorem globalPowerEval_surjective (Q : QuantumChain D) (B : PowerChainProperties Q) (r : ℕ) :
    Function.Surjective (globalPowerEval Q r) := by
  intro a
  obtain ⟨n, hn⟩ := Q.covers a
  let a' : Q.layer (n+1) := ⟨a, Q.increasing (Nat.le_succ n) hn⟩
  have hm := normalized_element_in_strip Q r n a'
  rw [← (chain_local_power_basis Q B r n).2] at hm
  obtain ⟨c, hc⟩ := hm
  refine ⟨fun i => (c i : D), ?_⟩
  apply (inverseInnerHom (gamma Q.x r (n+1))
    (gamma_ne_zero Q.x Q.not_rational r (n+1))).injective
  change (gamma Q.x r (n+1))⁻¹ * globalPowerEval Q r (fun i => (c i : D)) *
      gamma Q.x r (n+1) = _
  rw [globalPowerEval_normalization]
  exact hc

/-- The full condition (B), proved from the chain's explicit quantum/Ore/PBW
properties. As with (F), an actual model of the chain is still required. -/
theorem chain_global_right_basis (Q : QuantumChain D) (B : PowerChainProperties Q) (r : ℕ) :
    Function.Bijective (wideEval (imageField Q r).subtype
      (fun i : Fin (r+1) => (Q.x 0)^i.val)) := by
  let e := (kappa Q r).rangeRestrictFieldEquiv
  have heval (c : Fin (r+1) → imageField Q r) :
      globalPowerEval Q r (fun i => e.symm (c i)) =
        wideEval (imageField Q r).subtype (fun i : Fin (r+1) => (Q.x 0)^i.val) c := by
    unfold globalPowerEval wideEval
    apply Finset.sum_congr rfl
    intro i _
    change (Q.x 0)^i.val*kappa Q r (e.symm (c i)) = (Q.x 0)^i.val*(c i : D)
    dsimp only [e]
    rw [RingHom.rangeRestrictFieldEquiv_apply_symm_apply]
  constructor
  · intro c d h
    have he : (fun i => e.symm (c i)) = (fun i => e.symm (d i)) := by
      apply globalPowerEval_injective Q B r
      rw [heval, heval, h]
    funext i
    exact e.symm.injective (congrFun he i)
  · intro a
    obtain ⟨c, hc⟩ := globalPowerEval_surjective Q B r a
    refine ⟨fun i => e (c i), ?_⟩
    exact hc

end

end QuantumFlags

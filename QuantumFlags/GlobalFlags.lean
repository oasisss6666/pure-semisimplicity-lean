import QuantumFlags.CompatibleChain

namespace QuantumFlags

noncomputable section

variable {D : Type*} [DivisionRing D] [CharZero D]

theorem pair_layer (Q : QuantumChain D) (c : Fin 2 → D) :
    ∃ n, ∀ i, c i ∈ Q.layer n := by
  obtain ⟨n, h0, h1⟩ := common_layer Q (c 0) (c 1)
  refine ⟨n, ?_⟩
  intro i
  fin_cases i
  · exact h0
  · exact h1

def leftGlobalStrip (Q : QuantumChain D) (p : ℕ) (c : Fin 2 → D) : D :=
  kappa Q p (c 0) + kappa Q p (c 1)*Q.x 0

def rightGlobalStrip (Q : QuantumChain D) (p : ℕ) (c : Fin 2 → D) : D :=
  kappa Q p (c 0) + Q.x 0*kappa Q p (c 1)

theorem leftGlobalStrip_at (Q : QuantumChain D) (p n : ℕ) (c : Fin 2 → Q.layer n) :
    leftGlobalStrip Q p (fun i => (c i : D)) =
      leftConjugatedStrip (Q.layer n).subtype (Q.x 0) (gamma Q.x p n) c := by
  simp only [leftGlobalStrip, leftConjugatedStrip, Subfield.subtype_apply,
    kappa_at Q p n _ (c 0).property, kappa_at Q p n _ (c 1).property]

theorem rightGlobalStrip_at (Q : QuantumChain D) (p n : ℕ) (c : Fin 2 → Q.layer n) :
    rightGlobalStrip Q p (fun i => (c i : D)) =
      rightConjugatedStrip (Q.layer n).subtype (Q.x 0) (gamma Q.x p n) c := by
  simp only [rightGlobalStrip, rightConjugatedStrip, Subfield.subtype_apply,
    kappa_at Q p n _ (c 0).property, kappa_at Q p n _ (c 1).property]

theorem leftGlobalStrip_injective (Q : QuantumChain D) (p : ℕ) (hp : 1 ≤ p) :
    Function.Injective (leftGlobalStrip Q p) := by
  intro c d h
  obtain ⟨n, hn⟩ := pair_layer Q c
  obtain ⟨m, hm⟩ := pair_layer Q d
  let N := max n m
  let c' : Fin 2 → Q.layer N := fun i => ⟨c i, Q.increasing (le_max_left _ _) (hn i)⟩
  let d' : Fin 2 → Q.layer N := fun i => ⟨d i, Q.increasing (le_max_right _ _) (hm i)⟩
  have he := (chain_finite_adjacent_flags Q p N hp).1
  have h' : c' = d' := he (by
    rw [← leftGlobalStrip_at, ← leftGlobalStrip_at]
    exact h)
  funext i
  exact congrArg (fun a : Q.layer N => (a : D)) (congrFun h' i)

theorem rightGlobalStrip_injective (Q : QuantumChain D) (p : ℕ) (hp : 1 ≤ p) :
    Function.Injective (rightGlobalStrip Q (p+1)) := by
  intro c d h
  obtain ⟨n, hn⟩ := pair_layer Q c
  obtain ⟨m, hm⟩ := pair_layer Q d
  let N := max n m
  let c' : Fin 2 → Q.layer N := fun i => ⟨c i, Q.increasing (le_max_left _ _) (hn i)⟩
  let d' : Fin 2 → Q.layer N := fun i => ⟨d i, Q.increasing (le_max_right _ _) (hm i)⟩
  have he := (chain_finite_adjacent_flags Q p N hp).2.1
  have h' : c' = d' := he (by
    rw [← rightGlobalStrip_at, ← rightGlobalStrip_at]
    exact h)
  funext i
  exact congrArg (fun a : Q.layer N => (a : D)) (congrFun h' i)

theorem global_strip_ranges (Q : QuantumChain D) (p : ℕ) (hp : 1 ≤ p) :
    Set.range (leftGlobalStrip Q p) = Set.range (rightGlobalStrip Q (p+1)) := by
  ext z
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨n, hn⟩ := pair_layer Q c
    let c' : Fin 2 → Q.layer n := fun i => ⟨c i, hn i⟩
    have he := (chain_finite_adjacent_flags Q p n hp).2.2
    have hm : leftConjugatedStrip (Q.layer n).subtype (Q.x 0) (gamma Q.x p n) c' ∈
        Set.range (rightConjugatedStrip (Q.layer n).subtype (Q.x 0) (gamma Q.x (p+1) n)) :=
      he ▸ Set.mem_range_self c'
    obtain ⟨d, hd⟩ := hm
    refine ⟨fun i => (d i : D), ?_⟩
    rw [rightGlobalStrip_at, hd, ← leftGlobalStrip_at]
  · rintro ⟨c, rfl⟩
    obtain ⟨n, hn⟩ := pair_layer Q c
    let c' : Fin 2 → Q.layer n := fun i => ⟨c i, hn i⟩
    have he := (chain_finite_adjacent_flags Q p n hp).2.2
    have hm : rightConjugatedStrip (Q.layer n).subtype (Q.x 0) (gamma Q.x (p+1) n) c' ∈
        Set.range (leftConjugatedStrip (Q.layer n).subtype (Q.x 0) (gamma Q.x p n)) :=
      he.symm ▸ Set.mem_range_self c'
    obtain ⟨d, hd⟩ := hm
    refine ⟨fun i => (d i : D), ?_⟩
    rw [leftGlobalStrip_at, hd, ← rightGlobalStrip_at]

noncomputable abbrev imageField (Q : QuantumChain D) (p : ℕ) : Subfield D :=
  (kappa Q p).fieldRange

theorem left_image_strip_injective (Q : QuantumChain D) (p : ℕ) (hp : 1 ≤ p) :
    Function.Injective (leftEval (imageField Q p).subtype (Q.x 0)) := by
  let e := (kappa Q p).rangeRestrictFieldEquiv
  intro c d h
  have he : (fun i => e.symm (c i)) = (fun i => e.symm (d i)) := by
    apply leftGlobalStrip_injective Q p hp
    change kappa Q p (e.symm (c 0)) + kappa Q p (e.symm (c 1))*Q.x 0 =
      kappa Q p (e.symm (d 0)) + kappa Q p (e.symm (d 1))*Q.x 0
    dsimp only [e]
    rw [RingHom.rangeRestrictFieldEquiv_apply_symm_apply,
      RingHom.rangeRestrictFieldEquiv_apply_symm_apply,
      RingHom.rangeRestrictFieldEquiv_apply_symm_apply,
      RingHom.rangeRestrictFieldEquiv_apply_symm_apply]
    exact h
  funext i
  exact e.symm.injective (congrFun he i)

theorem right_image_strip_injective (Q : QuantumChain D) (p : ℕ) (hp : 1 ≤ p) :
    Function.Injective (rightEval (imageField Q (p+1)).subtype (Q.x 0)) := by
  let e := (kappa Q (p+1)).rangeRestrictFieldEquiv
  intro c d h
  have he : (fun i => e.symm (c i)) = (fun i => e.symm (d i)) := by
    apply rightGlobalStrip_injective Q p hp
    change kappa Q (p+1) (e.symm (c 0)) + Q.x 0*kappa Q (p+1) (e.symm (c 1)) =
      kappa Q (p+1) (e.symm (d 0)) + Q.x 0*kappa Q (p+1) (e.symm (d 1))
    dsimp only [e]
    rw [RingHom.rangeRestrictFieldEquiv_apply_symm_apply,
      RingHom.rangeRestrictFieldEquiv_apply_symm_apply,
      RingHom.rangeRestrictFieldEquiv_apply_symm_apply,
      RingHom.rangeRestrictFieldEquiv_apply_symm_apply]
    exact h
  funext i
  exact e.symm.injective (congrFun he i)

theorem left_image_strip_range (Q : QuantumChain D) (p : ℕ) :
    Set.range (leftEval (imageField Q p).subtype (Q.x 0)) =
      Set.range (leftGlobalStrip Q p) := by
  let e := (kappa Q p).rangeRestrictFieldEquiv
  ext z
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨fun i => e.symm (c i), ?_⟩
    change kappa Q p (e.symm (c 0)) + kappa Q p (e.symm (c 1))*Q.x 0 =
      (c 0 : D) + (c 1 : D)*Q.x 0
    dsimp only [e]
    rw [RingHom.rangeRestrictFieldEquiv_apply_symm_apply,
      RingHom.rangeRestrictFieldEquiv_apply_symm_apply]
  · rintro ⟨c, rfl⟩
    refine ⟨fun i => e (c i), ?_⟩
    change (e (c 0) : D) + (e (c 1) : D)*Q.x 0 =
      kappa Q p (c 0) + kappa Q p (c 1)*Q.x 0
    rfl

theorem right_image_strip_range (Q : QuantumChain D) (p : ℕ) :
    Set.range (rightEval (imageField Q p).subtype (Q.x 0)) =
      Set.range (rightGlobalStrip Q p) := by
  let e := (kappa Q p).rangeRestrictFieldEquiv
  ext z
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨fun i => e.symm (c i), ?_⟩
    change kappa Q p (e.symm (c 0)) + Q.x 0*kappa Q p (e.symm (c 1)) =
      (c 0 : D) + Q.x 0*(c 1 : D)
    dsimp only [e]
    rw [RingHom.rangeRestrictFieldEquiv_apply_symm_apply,
      RingHom.rangeRestrictFieldEquiv_apply_symm_apply]
  · rintro ⟨c, rfl⟩
    refine ⟨fun i => e (c i), ?_⟩
    change (e (c 0) : D) + Q.x 0*(e (c 1) : D) =
      kappa Q p (c 0) + Q.x 0*kappa Q p (c 1)
    rfl

/-- Condition (F), with both directness claims, for any quantum chain satisfying
the explicitly listed Ore/PBW properties. This does not establish existence
of such a chain. -/
theorem chain_global_adjacent_flags (Q : QuantumChain D) (p : ℕ) (hp : 1 ≤ p) :
    Function.Injective (leftEval (imageField Q p).subtype (Q.x 0)) ∧
    Function.Injective (rightEval (imageField Q (p+1)).subtype (Q.x 0)) ∧
    Set.range (leftEval (imageField Q p).subtype (Q.x 0)) =
      Set.range (rightEval (imageField Q (p+1)).subtype (Q.x 0)) := by
  refine ⟨left_image_strip_injective Q p hp, right_image_strip_injective Q p hp, ?_⟩
  rw [left_image_strip_range, global_strip_ranges Q p hp, right_image_strip_range]

end

end QuantumFlags

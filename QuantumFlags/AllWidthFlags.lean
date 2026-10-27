import QuantumFlags.PowerIndependence

namespace QuantumFlags

noncomputable section

variable {D : Type*} [DivisionRing D]

def leftPowerEval (H : Subfield D) (t : D) (e : ℕ) (c : Fin (e+1) → H) : D :=
  ∑ i, (c i : D)*t^i.val

theorem leftPowerEval_injective (S : FlagSystem D) (p : ℕ) (hp : 1 ≤ p) (e : ℕ) :
    Function.Injective (leftPowerEval (S.H p) S.t e) := by
  simpa only [Function.Injective, Fintype.linearCombination_apply, Subfield.smul_def,
    smul_eq_mul, leftPowerEval] using
    (left_powers_linearIndependent S p hp e).fintypeLinearCombination_injective

theorem leftPowerEval_range (S : FlagSystem D) (p e : ℕ) :
    Set.range (leftPowerEval (S.H p) S.t e) = (leftFlagSpan S p e : Set D) := by
  have he : leftPowerEval (S.H p) S.t e =
      (Fintype.linearCombination (S.H p) (fun i : Fin (e+1) => S.t^i.val) :
        (Fin (e+1) → S.H p) → D) := by
    funext c
    simp only [leftPowerEval, Fintype.linearCombination_apply, Subfield.smul_def, smul_eq_mul]
  rw [he, ← LinearMap.coe_range, Fintype.range_linearCombination,
    ← leftPowerSubmodule_eq_span]
  change ((leftPowerSubmodule (S.H p) S.t e).toAddSubgroup : Set D) = _
  rw [leftPowerSubmodule_group]

theorem power_mem_rightFlagSpan (S : FlagSystem D) (p e i : ℕ) (hi : i ≤ e) :
    S.t^i ∈ rightFlagSpan S p e := by
  induction e generalizing i with
  | zero =>
    have he : i = 0 := by omega
    subst i
    change S.t^0 ∈ S.H p
    simpa only [pow_zero] using (S.H p).one_mem
  | succ e ih =>
    change S.t^i ∈ rightFlagSpan S p e ⊔
      (rightFlagSpan S p e).map (AddMonoidHom.mulLeft S.t)
    by_cases hie : i ≤ e
    · exact AddSubgroup.mem_sup_left (ih i hie)
    · have hieq : i = e+1 := by omega
      subst i
      apply AddSubgroup.mem_sup_right
      exact AddSubgroup.mem_map.mpr ⟨S.t^e, ih e le_rfl, (pow_succ' S.t e).symm⟩

theorem rightPowerEval_range (S : FlagSystem D) (p e : ℕ) :
    Set.range (wideEval (S.H p).subtype (fun i : Fin (e+1) => S.t^i.val)) =
      (rightFlagSpan S p e : Set D) := by
  ext a
  constructor
  · rintro ⟨c, rfl⟩
    unfold wideEval
    apply AddSubgroup.sum_mem
    intro i _
    exact rightFlagSpan_mul S p e (c i) (c i).property _
      (power_mem_rightFlagSpan S p e i.val (Nat.le_of_lt_succ i.isLt))
  · intro ha
    have hs : a ∈ Submodule.span (S.H p)ᵐᵒᵖ
        (Set.range (fun i : Fin (e+1) => S.t^i.val)) := by
      apply rightFlagSpan_le_of_powers S p e
      · intro i hi
        exact Submodule.subset_span ⟨⟨i, Nat.lt_succ_of_le hi⟩, rfl⟩
      · exact ha
    rw [← Fintype.range_linearCombination] at hs
    obtain ⟨c, hc⟩ := hs
    refine ⟨fun i => (c i).unop, ?_⟩
    simpa only [Fintype.linearCombination_apply, rightSubfield_smul,
      wideEval, Subfield.subtype_apply] using hc

theorem flag_right_basis_linearIndependent (S : FlagSystem D) (r : ℕ) :
    LinearIndependent (S.H r)ᵐᵒᵖ (fun i : Fin (r+1) => S.t^i.val) := by
  apply linearIndependent_iff_injective_fintypeLinearCombination.mpr
  intro c d h
  apply (rightWideLinear_bijective _ _ (S.right_basis r)).injective
  change (∑ i, S.t^i.val*((c i).unop : D)) = (∑ i, S.t^i.val*((d i).unop : D))
  simpa only [Fintype.linearCombination_apply, rightSubfield_smul] using h

theorem flag_right_prefix_linearIndependent (S : FlagSystem D) (p e : ℕ) :
    LinearIndependent (S.H (p+e))ᵐᵒᵖ (fun i : Fin (e+1) => S.t^i.val) := by
  let f : Fin (e+1) → Fin (p+e+1) := fun i => ⟨i.val, by omega⟩
  have hf : Function.Injective f := by
    intro i j h
    exact Fin.ext (congrArg (fun a : Fin (p+e+1) => a.val) h)
  exact (flag_right_basis_linearIndependent S (p+e)).comp f hf

theorem flag_right_prefix_injective (S : FlagSystem D) (p e : ℕ) :
    Function.Injective (wideEval (S.H (p+e)).subtype
      (fun i : Fin (e+1) => S.t^i.val)) := by
  intro c d h
  have he : (fun i => MulOpposite.op (c i)) = (fun i => MulOpposite.op (d i)) := by
    apply (flag_right_prefix_linearIndependent S p e).fintypeLinearCombination_injective
    simpa only [Fintype.linearCombination_apply, rightSubfield_smul,
      MulOpposite.unop_op, wideEval, Subfield.subtype_apply] using h
  funext i
  exact MulOpposite.op_injective (congrFun he i)

/-- Proposition 4.1, including directness on both sides. -/
theorem all_width_direct_flags (S : FlagSystem D) (p : ℕ) (hp : 1 ≤ p) (e : ℕ) :
    Function.Injective (leftPowerEval (S.H p) S.t e) ∧
    Function.Injective (wideEval (S.H (p+e)).subtype
      (fun i : Fin (e+1) => S.t^i.val)) ∧
    Set.range (leftPowerEval (S.H p) S.t e) =
      Set.range (wideEval (S.H (p+e)).subtype (fun i : Fin (e+1) => S.t^i.val)) := by
  refine ⟨leftPowerEval_injective S p hp e, flag_right_prefix_injective S p e, ?_⟩
  rw [leftPowerEval_range, rightPowerEval_range]
  exact congrArg (fun A : AddSubgroup D => (A : Set D)) (all_width_span_equality S p hp e)

theorem actual_all_width_direct_flags (p : ℕ) (hp : 1 ≤ p) (e : ℕ) :
    Function.Injective (leftPowerEval (imageField actualQuantumChain p) (oreVariable 0) e) ∧
    Function.Injective (wideEval (imageField actualQuantumChain (p+e)).subtype
      (fun i : Fin (e+1) => (oreVariable 0)^i.val)) ∧
    Set.range (leftPowerEval (imageField actualQuantumChain p) (oreVariable 0) e) =
      Set.range (wideEval (imageField actualQuantumChain (p+e)).subtype
        (fun i : Fin (e+1) => (oreVariable 0)^i.val)) :=
  all_width_direct_flags actualFlagSystem p hp e

end

end QuantumFlags

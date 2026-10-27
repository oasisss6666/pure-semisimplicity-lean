import QuantumFlags.PowerSubmodules
import QuantumFlags.RightIndex

namespace QuantumFlags

noncomputable section

variable {D : Type*} [DivisionRing D]

def leftShiftRightLinear (H : Subfield D) (t : D) : D →ₗ[Hᵐᵒᵖ] D where
  toFun a := t*a
  map_add' a b := mul_add t a b
  map_smul' a b := by
    change t*(b*(a.unop : D)) = (t*b)*(a.unop : D)
    exact (mul_assoc _ _ _).symm

theorem iteratedAddSpan_mono (f : D →+ D) (e : ℕ) {A B : AddSubgroup D} (h : A ≤ B) :
    iteratedAddSpan f e A ≤ iteratedAddSpan f e B := by
  induction e with
  | zero => exact h
  | succ e ih => exact sup_le_sup ih (AddSubgroup.map_mono ih)

theorem rightFlagSpan_mul (S : FlagSystem D) (p e : ℕ) (c : D) (hc : c ∈ S.H p)
    (a : D) (ha : a ∈ rightFlagSpan S p e) : a*c ∈ rightFlagSpan S p e := by
  have hcomm : (AddMonoidHom.mulLeft S.t).comp (AddMonoidHom.mulRight c) =
      (AddMonoidHom.mulRight c).comp (AddMonoidHom.mulLeft S.t) := by
    ext x
    exact (mul_assoc S.t x c).symm
  have hb : (fieldAddGroup (S.H p)).map (AddMonoidHom.mulRight c) ≤ fieldAddGroup (S.H p) := by
    rintro b ⟨x, hx, rfl⟩
    exact (S.H p).mul_mem hx hc
  have hm : (rightFlagSpan S p e).map (AddMonoidHom.mulRight c) ≤ rightFlagSpan S p e := by
    unfold rightFlagSpan
    rw [← iteratedAddSpan_map _ _ hcomm]
    exact iteratedAddSpan_mono _ e hb
  exact hm (AddSubgroup.mem_map.mpr ⟨a, ha, rfl⟩)

theorem rightFlagSpan_le_of_powers (S : FlagSystem D) (p e : ℕ)
    (P : Submodule (S.H p)ᵐᵒᵖ D) (hP : ∀ i ≤ e, S.t^i ∈ P) :
    ∀ a ∈ rightFlagSpan S p e, a ∈ P := by
  induction e generalizing P with
  | zero =>
    intro a ha
    have h1 : (1 : D) ∈ P := by simpa only [pow_zero] using hP 0 le_rfl
    have hh := P.smul_mem (MulOpposite.op (⟨a, ha⟩ : S.H p)) h1
    simpa only [rightSubfield_smul, MulOpposite.unop_op, one_mul] using hh
  | succ e ih =>
    intro a ha
    obtain ⟨b, hb, c, hc, rfl⟩ := AddSubgroup.mem_sup.mp ha
    obtain ⟨d, hd, rfl⟩ := AddSubgroup.mem_map.mp hc
    apply P.add_mem (ih P (fun i hi => hP i (Nat.le_succ_of_le hi)) b hb)
    let f := leftShiftRightLinear (S.H p) S.t
    have hg : ∀ i ≤ e, S.t^i ∈ P.comap f := by
      intro i hi
      change S.t*S.t^i ∈ P
      rw [← pow_succ']
      exact hP (i+1) (Nat.succ_le_succ hi)
    exact ih (P.comap f) hg d hd

theorem rightFlagSpan_top_finrank_bound (S : FlagSystem D) (p e : ℕ)
    (h : rightFlagSpan S p e = ⊤) : Module.finrank (S.H p)ᵐᵒᵖ D ≤ e+1 := by
  let v : Fin (e+1) → D := fun i => S.t^i.val
  have htop : Submodule.span (S.H p)ᵐᵒᵖ (Set.range v) = ⊤ := by
    apply top_unique
    intro a _
    apply rightFlagSpan_le_of_powers S p e
    · intro i hi
      exact Submodule.subset_span ⟨⟨i, Nat.lt_succ_of_le hi⟩, rfl⟩
    · rw [h]
      trivial
  simpa only [Fintype.card_fin] using finrank_le_of_span_eq_top htop

end

end QuantumFlags

import QuantumFlags.RightSpanBounds
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

namespace QuantumFlags

noncomputable section

variable {D : Type*} [DivisionRing D]

theorem power_not_mem_previous (S : FlagSystem D) (p : ℕ) (hp : 1 ≤ p) (e : ℕ) :
    S.t^(e+1) ∉ leftPowerSubmodule (S.H p) S.t e := by
  intro he
  let L := leftPowerSubmodule (S.H p) S.t e
  have hstable : L.map (rightShiftLinear (S.H p) S.t) ≤ L := by
    rw [Submodule.map_le_iff_le_comap]
    apply leftPowerSubmodule_le_of_powers
    intro i hi
    change S.t^i*S.t ∈ L
    rw [← pow_succ]
    by_cases hie : i < e
    · exact power_mem_leftPowerSubmodule (S.H p) S.t e (i+1) (by omega)
    · have hieq : i = e := by omega
      subst i
      exact he
  have hnext : leftPowerSubmodule (S.H p) S.t (e+1) = L := by
    change L ⊔ L.map (rightShiftLinear (S.H p) S.t) = L
    exact sup_eq_left.mpr hstable
  have hright : L.toAddSubgroup = rightFlagSpan S (p+e) e :=
    (leftPowerSubmodule_group S p e).trans (all_width_span_equality S p hp e)
  have hrightNext : L.toAddSubgroup = rightFlagSpan S (p+(e+1)) (e+1) := by
    rw [← hnext]
    exact (leftPowerSubmodule_group S p (e+1)).trans (all_width_span_equality S p hp (e+1))
  let K := finiteRightStabilizer (S.H p) L
  have hcontains (j w : ℕ) (hL : L.toAddSubgroup = rightFlagSpan S j w) : S.H j ≤ K := by
    intro c hc
    change ∀ a ∈ L, a*c ∈ L
    intro a ha
    have ha' : a ∈ rightFlagSpan S j w := by rw [← hL]; exact ha
    have hb := rightFlagSpan_mul S j w c hc a ha'
    rw [← hL] at hb
    exact hb
  have hH : S.H (p+e) ≤ K := hcontains _ _ hright
  have hJ : S.H (p+e+1) ≤ K := by
    simpa only [Nat.add_assoc] using hcontains _ _ hrightNext
  have hKtop : K = ⊤ := consecutive_indices_force_top
    (S.H (p+e)) (S.H (p+e+1)) K hH hJ (p+e+1)
    (flag_right_finrank S (p+e)) (by simpa only [Nat.add_assoc] using flag_right_finrank S (p+e+1))
  have h1 : (1 : D) ∈ L := by
    simpa only [pow_zero] using power_mem_leftPowerSubmodule (S.H p) S.t e 0 (Nat.zero_le e)
  have hLtop : L = ⊤ := by
    apply top_unique
    intro a _
    have ha : a ∈ K := by rw [hKtop]; trivial
    have hb := (finiteRightStabilizer_mem_iff (S.H p) L a).mp ha 1 h1
    simpa only [one_mul] using hb
  have hRtop : rightFlagSpan S (p+e) e = ⊤ := by
    rw [← hright, hLtop]
    rfl
  have hbound := rightFlagSpan_top_finrank_bound S (p+e) e hRtop
  rw [flag_right_finrank] at hbound
  omega

theorem left_powers_linearIndependent (S : FlagSystem D) (p : ℕ) (hp : 1 ≤ p) (e : ℕ) :
    LinearIndependent (S.H p) (fun i : Fin (e+1) => S.t^i.val) := by
  induction e with
  | zero =>
    change LinearIndependent (S.H p) (fun i : Fin 1 => S.t^i.val)
    rw [linearIndependent_unique_iff]
    simp
  | succ e ih =>
    have hinit : Fin.init (fun i : Fin ((e+1)+1) => S.t^i.val) =
        (fun i : Fin (e+1) => S.t^i.val) := rfl
    rw [linearIndependent_finSucc', hinit]
    constructor
    · exact ih
    · simpa only [Fin.val_last, ← leftPowerSubmodule_eq_span] using power_not_mem_previous S p hp e

theorem left_dimension_infinite (S : FlagSystem D) (p : ℕ) (hp : 1 ≤ p) :
    ¬FiniteDimensional (S.H p) D := by
  intro h
  letI := h
  have hli := left_powers_linearIndependent S p hp (Module.finrank (S.H p) D)
  have hb := hli.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hb
  omega

theorem actual_left_dimension_infinite :
    ¬FiniteDimensional (imageField actualQuantumChain 1) OreUnion :=
  left_dimension_infinite actualFlagSystem 1 le_rfl

end

end QuantumFlags

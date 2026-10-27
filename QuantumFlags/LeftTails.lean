import QuantumFlags.PowerIndependence

namespace QuantumFlags

noncomputable section

variable {D : Type*} [DivisionRing D]

theorem all_left_powers_linearIndependent (S : FlagSystem D) (p : ℕ) (hp : 1 ≤ p) :
    LinearIndependent (S.H p) (fun i : ℕ => S.t^i) := by
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  let m := s.sup id
  let f : s → Fin (m+1) := fun i => ⟨i.val, Nat.lt_succ_of_le (Finset.le_sup (f := id) i.property)⟩
  have hf : Function.Injective f := by
    intro i j h
    apply Subtype.ext
    exact congrArg (fun a : Fin (m+1) => a.val) h
  exact (left_powers_linearIndependent S p hp m).comp f hf

def leftTail (S : FlagSystem D) (k : ℕ) : Submodule (S.H 1) D :=
  Submodule.span (S.H 1) ((fun i : ℕ => S.t^i) '' Set.Ici k)

theorem leftTail_antitone (S : FlagSystem D) : Antitone (leftTail S) := by
  intro k l hkl
  apply Submodule.span_mono
  rintro x ⟨i,hi,rfl⟩
  exact ⟨i,le_trans hkl hi,rfl⟩

theorem power_mem_leftTail (S : FlagSystem D) (k : ℕ) : S.t^k ∈ leftTail S k :=
  Submodule.subset_span ⟨k,Set.mem_Ici.mpr le_rfl,rfl⟩

theorem power_not_mem_next_leftTail (S : FlagSystem D) (k : ℕ) :
    S.t^k ∉ leftTail S (k+1) :=
  (all_left_powers_linearIndependent S 1 le_rfl).notMem_span_image (by simp)

theorem leftTail_succ_lt (S : FlagSystem D) (k : ℕ) : leftTail S (k+1) < leftTail S k := by
  apply lt_of_le_of_ne (leftTail_antitone S (by omega))
  intro h
  have hm := power_mem_leftTail S k
  rw [← h] at hm
  exact power_not_mem_next_leftTail S k hm

theorem leftTail_strictAnti (S : FlagSystem D) : StrictAnti (leftTail S) :=
  strictAnti_nat_of_succ_lt (leftTail_succ_lt S)

theorem actual_leftTail_strictAnti : StrictAnti (leftTail actualFlagSystem) :=
  leftTail_strictAnti actualFlagSystem

end

end QuantumFlags

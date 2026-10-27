import QuantumFlags.FiniteStabilizer

namespace QuantumFlags

noncomputable section

variable {D : Type*} [DivisionRing D]

def fieldLeftLinear (H : Subfield D) : H →ₗ[H] D where
  toFun := (↑)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rightShiftLinear (H : Subfield D) (t : D) : D →ₗ[H] D where
  toFun a := a*t
  map_add' a b := add_mul a b t
  map_smul' a b := mul_assoc (a : D) b t

def leftPowerSubmodule (H : Subfield D) (t : D) : ℕ → Submodule H D
  | 0 => (fieldLeftLinear H).range
  | e+1 => leftPowerSubmodule H t e ⊔
      (leftPowerSubmodule H t e).map (rightShiftLinear H t)

instance leftPowerSubmodule_finite (H : Subfield D) (t : D) (e : ℕ) :
    FiniteDimensional H (leftPowerSubmodule H t e) := by
  induction e with
  | zero => change FiniteDimensional H (fieldLeftLinear H).range; infer_instance
  | succ e ih =>
    letI := ih
    change FiniteDimensional H ((leftPowerSubmodule H t e ⊔
      (leftPowerSubmodule H t e).map (rightShiftLinear H t)) : Submodule H D)
    infer_instance

theorem module_sup_group (H : Subfield D) (A B : Submodule H D) :
    (A ⊔ B).toAddSubgroup = A.toAddSubgroup ⊔ B.toAddSubgroup := by
  ext a
  change a ∈ A ⊔ B ↔ a ∈ A.toAddSubgroup ⊔ B.toAddSubgroup
  rw [Submodule.mem_sup, AddSubgroup.mem_sup]
  rfl

theorem module_map_group (H : Subfield D) (A : Submodule H D) (f : D →ₗ[H] D) :
    (A.map f).toAddSubgroup = A.toAddSubgroup.map f.toAddMonoidHom := by
  ext a
  rfl

theorem leftPowerSubmodule_group (S : FlagSystem D) (p e : ℕ) :
    (leftPowerSubmodule (S.H p) S.t e).toAddSubgroup = leftFlagSpan S p e := by
  induction e with
  | zero =>
    ext a
    change (∃ b : S.H p, (b : D) = a) ↔ a ∈ S.H p
    exact ⟨fun ⟨b, hb⟩ => hb ▸ b.property, fun h => ⟨⟨a, h⟩, rfl⟩⟩
  | succ e ih =>
    rw [leftPowerSubmodule, module_sup_group, module_map_group, ih]
    rfl

theorem power_mem_leftPowerSubmodule (H : Subfield D) (t : D) (e i : ℕ) (hi : i ≤ e) :
    t^i ∈ leftPowerSubmodule H t e := by
  induction e generalizing i with
  | zero =>
    have he : i = 0 := by omega
    subst i
    exact ⟨1, by simp [fieldLeftLinear]⟩
  | succ e ih =>
    change t^i ∈ leftPowerSubmodule H t e ⊔
      (leftPowerSubmodule H t e).map (rightShiftLinear H t)
    by_cases hie : i ≤ e
    · exact Submodule.mem_sup_left (ih i hie)
    · have he : i = e+1 := by omega
      subst i
      apply Submodule.mem_sup_right
      exact Submodule.mem_map.mpr ⟨t^e, ih e le_rfl, (pow_succ t e).symm⟩

theorem leftPowerSubmodule_le_of_powers (H : Subfield D) (t : D) (e : ℕ)
    (P : Submodule H D) (hP : ∀ i ≤ e, t^i ∈ P) : leftPowerSubmodule H t e ≤ P := by
  induction e generalizing P with
  | zero =>
    intro a ha
    obtain ⟨b, rfl⟩ := ha
    have h1 : (1 : D) ∈ P := by simpa only [pow_zero] using hP 0 le_rfl
    simpa only [fieldLeftLinear, LinearMap.coe_mk, AddHom.coe_mk,
      Subfield.smul_def, smul_eq_mul, mul_one] using P.smul_mem b h1
  | succ e ih =>
    apply sup_le
    · exact ih P (fun i hi => hP i (Nat.le_step hi))
    · rw [Submodule.map_le_iff_le_comap]
      apply ih
      intro i hi
      change t^i*t ∈ P
      rw [← pow_succ]
      exact hP (i+1) (Nat.succ_le_succ hi)

theorem leftPowerSubmodule_eq_span (H : Subfield D) (t : D) (e : ℕ) :
    leftPowerSubmodule H t e =
      Submodule.span H (Set.range (fun i : Fin (e+1) => t^i.val)) := by
  apply le_antisymm
  · apply leftPowerSubmodule_le_of_powers
    intro i hi
    exact Submodule.subset_span ⟨⟨i, Nat.lt_succ_of_le hi⟩, rfl⟩
  · apply Submodule.span_le.mpr
    rintro a ⟨i, rfl⟩
    exact power_mem_leftPowerSubmodule H t e i.val (Nat.le_of_lt_succ i.isLt)

end

end QuantumFlags

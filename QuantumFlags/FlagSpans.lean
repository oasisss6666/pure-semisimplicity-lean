import QuantumFlags.FlagSystem
import Mathlib.Algebra.Group.Subgroup.Basic

namespace QuantumFlags

noncomputable section

variable {D : Type*} [DivisionRing D]

/-- The additive span of A,f(A),...,f^e(A). Repeated summands are harmless. -/
def iteratedAddSpan (f : D →+ D) : ℕ → AddSubgroup D → AddSubgroup D
  | 0, A => A
  | e+1, A => iteratedAddSpan f e A ⊔ (iteratedAddSpan f e A).map f

theorem iteratedAddSpan_sup (f : D →+ D) (e : ℕ) (A B : AddSubgroup D) :
    iteratedAddSpan f e (A ⊔ B) = iteratedAddSpan f e A ⊔ iteratedAddSpan f e B := by
  induction e with
  | zero => rfl
  | succ e ih =>
    simp only [iteratedAddSpan, ih, AddSubgroup.map_sup]
    exact sup_sup_sup_comm _ _ _ _

theorem iteratedAddSpan_map (f g : D →+ D) (hfg : f.comp g = g.comp f)
    (e : ℕ) (A : AddSubgroup D) :
    iteratedAddSpan f e (A.map g) = (iteratedAddSpan f e A).map g := by
  induction e with
  | zero => rfl
  | succ e ih =>
    simp only [iteratedAddSpan, ih, AddSubgroup.map_sup, AddSubgroup.map_map, hfg]

theorem iteratedAddSpan_expand (f : D →+ D) (e : ℕ) (A : AddSubgroup D) :
    iteratedAddSpan f e (A ⊔ A.map f) = iteratedAddSpan f (e+1) A := by
  rw [iteratedAddSpan_sup, iteratedAddSpan_map f f rfl]
  rfl

def fieldAddGroup (H : Subfield D) : AddSubgroup D := H.toSubring.toAddSubgroup

def leftFlagSpan (S : FlagSystem D) (p e : ℕ) : AddSubgroup D :=
  iteratedAddSpan (AddMonoidHom.mulRight S.t) e (fieldAddGroup (S.H p))

def rightFlagSpan (S : FlagSystem D) (p e : ℕ) : AddSubgroup D :=
  iteratedAddSpan (AddMonoidHom.mulLeft S.t) e (fieldAddGroup (S.H p))

theorem field_strip_left_range (H : Subfield D) (t : D) :
    (((fieldAddGroup H ⊔ (fieldAddGroup H).map (AddMonoidHom.mulRight t)) : AddSubgroup D) : Set D) =
      Set.range (leftEval H.subtype t) := by
  ext z
  constructor
  · intro hz
    obtain ⟨a, ha, b, hb, hab⟩ := AddSubgroup.mem_sup.mp hz
    obtain ⟨c, hc, rfl⟩ := AddSubgroup.mem_map.mp hb
    exact ⟨![⟨a, ha⟩, ⟨c, hc⟩], hab⟩
  · rintro ⟨c, rfl⟩
    exact AddSubgroup.mem_sup.mpr ⟨c 0, (c 0).property, (c 1 : D)*t,
      AddSubgroup.mem_map.mpr ⟨c 1, (c 1).property, rfl⟩, rfl⟩

theorem field_strip_right_range (H : Subfield D) (t : D) :
    (((fieldAddGroup H ⊔ (fieldAddGroup H).map (AddMonoidHom.mulLeft t)) : AddSubgroup D) : Set D) =
      Set.range (rightEval H.subtype t) := by
  ext z
  constructor
  · intro hz
    obtain ⟨a, ha, b, hb, hab⟩ := AddSubgroup.mem_sup.mp hz
    obtain ⟨c, hc, rfl⟩ := AddSubgroup.mem_map.mp hb
    exact ⟨![⟨a, ha⟩, ⟨c, hc⟩], hab⟩
  · rintro ⟨c, rfl⟩
    exact AddSubgroup.mem_sup.mpr ⟨c 0, (c 0).property, t*(c 1 : D),
      AddSubgroup.mem_map.mpr ⟨c 1, (c 1).property, rfl⟩, rfl⟩

theorem adjacent_add_groups (S : FlagSystem D) (p : ℕ) (hp : 1 ≤ p) :
    fieldAddGroup (S.H p) ⊔ (fieldAddGroup (S.H p)).map (AddMonoidHom.mulRight S.t) =
      fieldAddGroup (S.H (p+1)) ⊔
        (fieldAddGroup (S.H (p+1))).map (AddMonoidHom.mulLeft S.t) := by
  apply SetLike.coe_injective
  rw [field_strip_left_range, field_strip_right_range]
  exact (S.adjacent p hp).2.2

/-- The equality of the two finite spans in Proposition 4.1. Left directness
requires the separate finite-index argument and is not asserted here. -/
theorem all_width_span_equality (S : FlagSystem D) (p : ℕ) (hp : 1 ≤ p) (e : ℕ) :
    leftFlagSpan S p e = rightFlagSpan S (p+e) e := by
  have hcomm : (AddMonoidHom.mulLeft S.t).comp (AddMonoidHom.mulRight S.t) =
      (AddMonoidHom.mulRight S.t).comp (AddMonoidHom.mulLeft S.t) := by
    ext a
    exact (mul_assoc S.t a S.t).symm
  induction e with
  | zero => simp only [leftFlagSpan, rightFlagSpan, iteratedAddSpan, Nat.add_zero]
  | succ e ih =>
    change leftFlagSpan S p e ⊔ (leftFlagSpan S p e).map (AddMonoidHom.mulRight S.t) = _
    rw [ih]
    unfold rightFlagSpan
    rw [← iteratedAddSpan_map _ _ hcomm,
      ← iteratedAddSpan_sup, adjacent_add_groups S (p+e) (by omega), iteratedAddSpan_expand]
    rfl

end

end QuantumFlags

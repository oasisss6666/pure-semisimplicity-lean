import QuantumFlags.RightDimensions

namespace QuantumFlags

noncomputable section

variable {D : Type*} [DivisionRing D]

theorem right_index_dvd (H S : Subfield D) (h : H ≤ S) :
    Module.finrank Sᵐᵒᵖ D ∣ Module.finrank Hᵐᵒᵖ D := by
  letI : Module Hᵐᵒᵖ Sᵐᵒᵖ := Module.compHom Sᵐᵒᵖ (Subfield.inclusion h).op
  letI : IsScalarTower Hᵐᵒᵖ Sᵐᵒᵖ D := ⟨by
    intro a b c
    change c*((b.unop : D)*(a.unop : D)) = (c*(b.unop : D))*(a.unop : D)
    exact (mul_assoc _ _ _).symm⟩
  exact Module.finrank_dvd_finrank_left Hᵐᵒᵖ Sᵐᵒᵖ D

def rightInclusionLinear (S : Subfield D) : Sᵐᵒᵖ →ₗ[Sᵐᵒᵖ] D where
  toFun a := (a.unop : D)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem right_index_one_top (S : Subfield D) (hd : Module.finrank Sᵐᵒᵖ D = 1) : S = ⊤ := by
  letI : FiniteDimensional Sᵐᵒᵖ D := FiniteDimensional.of_finrank_eq_succ (n := 0) hd
  have hi : Function.Injective (rightInclusionLinear S) := by
    intro a b h
    exact MulOpposite.unop_injective (Subtype.ext h)
  have hsur : Function.Surjective (rightInclusionLinear S) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := rightInclusionLinear S) (by rw [Module.finrank_self, hd])).mp hi
  apply top_unique
  intro a _
  obtain ⟨b, hb⟩ := hsur a
  exact hb ▸ b.unop.property

theorem consecutive_indices_force_top (H K S : Subfield D) (hH : H ≤ S) (hK : K ≤ S)
    (n : ℕ) (hdH : Module.finrank Hᵐᵒᵖ D = n) (hdK : Module.finrank Kᵐᵒᵖ D = n+1) :
    S = ⊤ := by
  apply right_index_one_top S
  have hdivH := right_index_dvd H S hH
  have hdivK := right_index_dvd K S hK
  rw [hdH] at hdivH
  rw [hdK] at hdivK
  exact Nat.dvd_one.mp ((Nat.dvd_add_iff_right hdivH).mpr hdivK)

end

end QuantumFlags

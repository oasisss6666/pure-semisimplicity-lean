import QuantumFlags.EquivalenceIndecomposable
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

namespace QuantumFlags
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u₁ v₁ u₂ v₂
variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasBinaryBiproducts C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasBinaryBiproducts D]

theorem faithful_isZero_iff (F : C ⥤ D) [F.Faithful] [F.Additive] (X : C) :
    IsZero (F.obj X) ↔ IsZero X := by
  simp only [IsZero.iff_id_eq_zero]
  constructor
  · intro h
    apply F.map_injective
    simpa only [F.map_id, F.map_zero] using h
  · intro h
    rw [← F.map_id, h, F.map_zero]

/-- A full faithful additive embedding whose image is closed under actual retracts
reflects the ambient meaning of indecomposability. -/
theorem retract_closed_indecomposable_iff (F : C ⥤ D) [F.Full] [F.Faithful] [F.Additive]
    (closed : ∀ (X : C) (Y : D) (i : Y ⟶ F.obj X) (p : F.obj X ⟶ Y),
      i ≫ p = 𝟙 Y → ∃ Y' : C, Nonempty (F.obj Y' ≅ Y)) (X : C) :
    Indecomposable (F.obj X) ↔ Indecomposable X := by
  letI : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
  constructor
  · intro h
    constructor
    · intro hX
      exact h.1 ((faithful_isZero_iff F X).mpr hX)
    · intro Y Z α
      have h' := h.2 (F.obj Y) (F.obj Z) (F.mapIso α ≪≫ F.mapBiprod Y Z)
      exact h'.imp ((faithful_isZero_iff F Y).mp) ((faithful_isZero_iff F Z).mp)
  · intro h
    constructor
    · intro hX
      exact h.1 ((faithful_isZero_iff F X).mp hX)
    · intro Y Z α
      obtain ⟨Y', ⟨eY⟩⟩ := closed X Y (biprod.inl ≫ α.inv) (α.hom ≫ biprod.fst)
        (by simp)
      obtain ⟨Z', ⟨eZ⟩⟩ := closed X Z (biprod.inr ≫ α.inv) (α.hom ≫ biprod.snd)
        (by simp)
      let β : X ≅ Y' ⊞ Z' := F.preimageIso
        (α ≪≫ biprod.mapIso eY.symm eZ.symm ≪≫ (F.mapBiprod Y' Z').symm)
      rcases h.2 Y' Z' β with hY | hZ
      · exact Or.inl (eY.isZero_iff.mp (F.map_isZero hY))
      · exact Or.inr (eZ.isZero_iff.mp (F.map_isZero hZ))

end
end QuantumFlags

import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Preadditive.Biproducts

namespace QuantumFlags
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D]

theorem equivalence_isZero_iff (e : C ≌ D) (X : C) :
    IsZero (e.functor.obj X) ↔ IsZero X := by
  simp only [IsZero.iff_id_eq_zero]
  constructor
  · intro h
    apply e.functor.map_injective
    simpa only [e.functor.map_id, e.functor.map_zero] using h
  · intro h
    rw [← e.functor.map_id, h, e.functor.map_zero]

variable [HasBinaryBiproducts C] [HasBinaryBiproducts D]

theorem equivalence_indecomposable_iff (e : C ≌ D) (X : C) :
    Indecomposable (e.functor.obj X) ↔ Indecomposable X := by
  letI : PreservesBinaryBiproducts e.functor :=
    preservesBinaryBiproducts_of_preservesBinaryProducts e.functor
  letI : PreservesBinaryBiproducts e.inverse :=
    preservesBinaryBiproducts_of_preservesBinaryProducts e.inverse
  constructor
  · intro h
    constructor
    · intro hX
      exact h.1 ((equivalence_isZero_iff e X).mpr hX)
    · intro Y Z α
      have h' := h.2 (e.functor.obj Y) (e.functor.obj Z)
        (e.functor.mapIso α ≪≫ e.functor.mapBiprod Y Z)
      exact h'.imp ((equivalence_isZero_iff e Y).mp) ((equivalence_isZero_iff e Z).mp)
  · intro h
    constructor
    · intro hX
      exact h.1 ((equivalence_isZero_iff e X).mp hX)
    · intro Y Z α
      have h' := h.2 (e.inverse.obj Y) (e.inverse.obj Z)
        (e.unitIso.app X ≪≫ e.inverse.mapIso α ≪≫ e.inverse.mapBiprod Y Z)
      rcases h' with hY | hZ
      · exact Or.inl ((e.counitIso.app Y).isZero_iff.mp (e.functor.map_isZero hY))
      · exact Or.inr ((e.counitIso.app Z).isZero_iff.mp (e.functor.map_isZero hZ))

end
end QuantumFlags

import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Ring.Equiv

namespace QuantumFlags
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

theorem indecomposable_of_trivial_end_idempotents (X : C)
    (hne : (𝟙 X : X ⟶ X) ≠ 0)
    (hid : ∀ f : End X, f*f = f → f = 0 ∨ f = 1) : Indecomposable X := by
  constructor
  · intro h
    exact hne ((IsZero.iff_id_eq_zero X).mp h)
  · intro Y Z α
    let e : End X := α.hom ≫ biprod.fst ≫ biprod.inl ≫ α.inv
    have he : e*e = e := by
      change e ≫ e = e
      simp [e, Category.assoc]
    rcases hid e he with h0 | h1
    · apply Or.inl
      apply (IsZero.iff_id_eq_zero Y).mpr
      have h := congrArg (fun f : End X =>
        (biprod.inl : Y ⟶ Y ⊞ Z) ≫ α.inv ≫ f ≫ α.hom ≫ biprod.fst) h0
      simpa [e, Category.assoc] using h
    · apply Or.inr
      apply (IsZero.iff_id_eq_zero Z).mpr
      have h := congrArg (fun f : End X =>
        (biprod.inr : Z ⟶ Y ⊞ Z) ≫ α.inv ≫ f ≫ α.hom ≫ biprod.snd) h1
      simpa [e, Category.assoc] using h.symm

theorem indecomposable_of_endRingEquiv_division (X : C) {K : Type*} [DivisionRing K]
    (e : End X ≃+* K) : Indecomposable X := by
  apply indecomposable_of_trivial_end_idempotents X
  · intro h
    have he : e (1 : End X) = e 0 := congrArg e h
    exact one_ne_zero (by simpa only [map_one, map_zero] using he)
  · intro f hf
    have hi : e f * e f = e f := by rw [← map_mul, hf]
    have hz : e f * (e f - 1) = 0 := by rw [mul_sub, hi, mul_one, sub_self]
    rcases mul_eq_zero.mp hz with h0 | h1
    · left
      apply e.injective
      simpa only [map_zero] using h0
    · right
      apply e.injective
      simpa only [map_one] using (sub_eq_zero.mp h1)

end
end QuantumFlags

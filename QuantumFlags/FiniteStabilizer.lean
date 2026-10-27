import QuantumFlags.FlagSpans
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace QuantumFlags

noncomputable section

variable {D : Type*} [DivisionRing D] (H : Subfield D)

def stabilizerEndomorphism (L : Submodule H D) (s : D)
    (hs : ∀ a ∈ L, a*s ∈ L) : L →ₗ[H] L where
  toFun a := ⟨(a : D)*s, hs a a.property⟩
  map_add' a b := Subtype.ext (add_mul (a : D) (b : D) s)
  map_smul' c a := by
    apply Subtype.ext
    exact mul_assoc (c : D) (a : D) s

theorem finite_stabilizer_inverse (L : Submodule H D) [FiniteDimensional H L]
    (s : D) (hs : ∀ a ∈ L, a*s ∈ L) (hs0 : s ≠ 0) :
    ∀ a ∈ L, a*s⁻¹ ∈ L := by
  let f := stabilizerEndomorphism H L s hs
  have hi : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply mul_right_cancel₀ hs0
    exact congrArg (fun a : L => (a : D)) hab
  have hsur : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hi
  intro a ha
  obtain ⟨b, hb⟩ := hsur ⟨a, ha⟩
  have he : (b : D)*s = a := congrArg (fun a : L => (a : D)) hb
  have hei : a*s⁻¹ = (b : D) := by
    rw [← he, mul_assoc, mul_inv_cancel₀ hs0, mul_one]
  rw [hei]
  exact b.property

/-- The right stabilizer of a finite-dimensional left H-space is an actual
division subring of the ambient division ring. -/
def finiteRightStabilizer (L : Submodule H D) [FiniteDimensional H L] : Subfield D where
  carrier := {s | ∀ a ∈ L, a*s ∈ L}
  zero_mem' a _ := by simpa only [mul_zero] using L.zero_mem
  one_mem' a ha := by simpa only [mul_one] using ha
  add_mem' hs ht a ha := by
    rw [mul_add]
    exact L.add_mem (hs a ha) (ht a ha)
  neg_mem' hs a ha := by
    rw [mul_neg]
    exact L.neg_mem (hs a ha)
  mul_mem' hs ht a ha := by
    rw [← mul_assoc]
    exact ht _ (hs a ha)
  inv_mem' {s} hs := by
    by_cases hz : s = 0
    · subst s
      intro a _
      simpa only [inv_zero, mul_zero] using L.zero_mem
    · exact finite_stabilizer_inverse H L s hs hz

theorem finiteRightStabilizer_mem_iff (L : Submodule H D) [FiniteDimensional H L] (s : D) :
    s ∈ finiteRightStabilizer H L ↔ ∀ a ∈ L, a*s ∈ L := Iff.rfl

end

end QuantumFlags

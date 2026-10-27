import QuantumFlags.TriangularRing
import Mathlib.RingTheory.Artinian.Defs
import Mathlib.Order.WellFounded

namespace QuantumFlags

noncomputable section

variable {D : Type*} [DivisionRing D]

theorem triangular_not_left_artinian (S : FlagSystem D) :
    ¬ IsArtinianRing (TriangularRing (S.H 1)) := by
  intro h
  letI := h
  have wf : WellFounded ((· < ·) : Ideal (TriangularRing (S.H 1)) →
      Ideal (TriangularRing (S.H 1)) → Prop) := wellFounded_lt
  exact (wellFounded_iff_isEmpty_descending_chain.mp wf).false
    ⟨fun k => cornerLeftIdeal (S.H 1) (leftTail S k),
      fun k => triangular_left_ideal_chain S (Nat.lt_succ_self k)⟩

theorem actual_triangular_not_left_artinian :
    ¬ IsArtinianRing (TriangularRing (actualFlagSystem.H 1)) :=
  triangular_not_left_artinian actualFlagSystem

end

end QuantumFlags

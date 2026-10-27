import QuantumFlags.IteratedStripDuals

namespace QuantumFlags

noncomputable section

/-- A closed existence statement for the division-ring-extension part of the manuscript.
The iterates below are actual right-linear Hom duals, with precomposition on the right. -/
theorem actual_generalized_artin_extension :
    ∃ H : Subfield OreUnion,
      (¬ FiniteDimensional H OreUnion) ∧
      (∀ n : ℕ, FiniteDimensional (iteratedRightDual (ambientBimodule H) n).RightRingᵐᵒᵖ
        (iteratedRightDual (ambientBimodule H) n).Space) ∧
      (∀ n : ℕ, Module.finrank (iteratedRightDual (ambientBimodule H) n).RightRingᵐᵒᵖ
        (iteratedRightDual (ambientBimodule H) n).Space = if n = 0 then 1 else 2) := by
  refine ⟨actualFlagSystem.H 1, actual_left_dimension_infinite, ?_, ?_⟩
  · exact iterated_right_dual_finite actualFlagSystem
  · exact actual_right_dimension_sequence

end

end QuantumFlags

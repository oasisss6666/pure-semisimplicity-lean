import QuantumFlags.PreinjectiveFamily
import QuantumFlags.IteratedStripDuals

namespace QuantumFlags
noncomputable section
open CategoryTheory
universe u v
variable {D : Type u} [DivisionRing D]

def flagReflectionChain (S : FlagSystem D) :
    RightReflectionChain (ambientBimodule (S.H 1)) where
  finite := iterated_right_dual_finite S
  double r := by
    rw [right_dimension_sequence]
    simp

def actualReflectionChain :
    RightReflectionChain (ambientBimodule (actualFlagSystem.H 1)) :=
  flagReflectionChain actualFlagSystem

abbrev actualPreinjective (k : ℕ) := preinjectiveRepresentation.{0,v} actualReflectionChain k

local instance actualPreinjectiveSourceModule (k : ℕ) :
    Module (actualFlagSystem.H 1)ᵐᵒᵖ (actualPreinjective.{v} k).Source :=
  (actualPreinjective k).sourceModule

local instance actualPreinjectiveTargetModule (k : ℕ) :
    Module OreUnionᵐᵒᵖ (actualPreinjective.{v} k).Target :=
  (actualPreinjective k).targetModule

theorem actualPreinjective_dimension_vector (k : ℕ) :
    (Module.finrank (actualFlagSystem.H 1)ᵐᵒᵖ (actualPreinjective.{v} k).Source,
      Module.finrank OreUnionᵐᵒᵖ (actualPreinjective.{v} k).Target) = (k+1,k) :=
  preinjectiveRepresentation_dimension_vector actualReflectionChain k

theorem actualPreinjective_indecomposable (k : ℕ) :
    CategoryTheory.Indecomposable (actualPreinjective.{v} k) :=
  preinjectiveFamily_indecomposable actualReflectionChain k 0

theorem actualPreinjective_pairwise_nonisomorphic {k l : ℕ} (h : k ≠ l) :
    ¬ Nonempty (actualPreinjective.{v} k ≅ actualPreinjective.{v} l) :=
  preinjectiveRepresentation_pairwise_nonisomorphic actualReflectionChain h

end
end QuantumFlags

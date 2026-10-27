import QuantumFlags.FiniteRightModuleClassification
import QuantumFlags.ActualPreinjectiveModules

namespace QuantumFlags
noncomputable section
open CategoryTheory
universe v

abbrev ActualCounterexampleBimodule := ambientBimodule (actualFlagSystem.H 1)

local instance actualClassificationSourceModule
    (M : TensorRepresentation.{0,v,v} ActualCounterexampleBimodule) :
    Module (actualFlagSystem.H 1)ᵐᵒᵖ M.Source := M.sourceModule

local instance actualClassificationTargetModule
    (M : TensorRepresentation.{0,v,v} ActualCounterexampleBimodule) :
    Module OreUnionᵐᵒᵖ M.Target := M.targetModule

theorem actualFiniteIndecomposable_classification
    (M : TensorRepresentation.{0,v,v} ActualCounterexampleBimodule)
    [FiniteDimensional ActualCounterexampleBimodule.LeftRingᵐᵒᵖ M.Source]
    [FiniteDimensional ActualCounterexampleBimodule.RightRingᵐᵒᵖ M.Target]
    (hM : Indecomposable M) :
    Nonempty (M ≅ tensorSimpleSource.{0,v} ActualCounterexampleBimodule) ∨
    Nonempty (M ≅ tensorSimpleTarget.{0,v} ActualCounterexampleBimodule) ∨
    Nonempty (M ≅ tensorCanonicalProjective.{0,v} ActualCounterexampleBimodule) ∨
    ∃ k : ℕ, 0 < k ∧ Nonempty (M ≅ actualPreinjective.{v} k) := by
  apply finiteIndecomposable_classification actualReflectionChain _ M hM
  exact Module.finrank_eq_of_rank_eq (ambient_right_rank_one (actualFlagSystem.H 1))

theorem actualFiniteRightModule_indecomposable_classification
    (M : ModuleCat.{v} (BimoduleTriangularRing ActualCounterexampleBimodule)ᵐᵒᵖ)
    [Module.Finite (BimoduleTriangularRing ActualCounterexampleBimodule)ᵐᵒᵖ M]
    (hM : Indecomposable M) :
    Nonempty (M ≅ (bimoduleTensorRepresentationEquivalence ActualCounterexampleBimodule).functor.obj
      (tensorSimpleSource.{0,v} ActualCounterexampleBimodule)) ∨
    Nonempty (M ≅ (bimoduleTensorRepresentationEquivalence ActualCounterexampleBimodule).functor.obj
      (tensorSimpleTarget.{0,v} ActualCounterexampleBimodule)) ∨
    Nonempty (M ≅ (bimoduleTensorRepresentationEquivalence ActualCounterexampleBimodule).functor.obj
      (tensorCanonicalProjective.{0,v} ActualCounterexampleBimodule)) ∨
    ∃ k : ℕ, 0 < k ∧ Nonempty (M ≅ actualPreinjectiveRightModule.{v} k) := by
  apply finiteRightModule_indecomposable_classification actualReflectionChain _ M hM
  exact Module.finrank_eq_of_rank_eq (ambient_right_rank_one (actualFlagSystem.H 1))

end
end QuantumFlags

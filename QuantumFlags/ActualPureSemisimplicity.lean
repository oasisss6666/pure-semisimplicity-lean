import QuantumFlags.PureSemisimplicity
import QuantumFlags.ActualFiniteClassification
import QuantumFlags.BimoduleAmbientComparison
import QuantumFlags.LeftArtinianObstruction

/-!
# Right pure semisimplicity of the actual counterexample ring

Manuscript `thm:pss` applied to `H ⊆ T` (source line 415): the actual Ore model supplies the right
dimension sequence `(1,2,2,...)`, so the triangular ring `R_N` of `N = ₕT_T` is right pure
semisimple and has infinitely many isomorphism classes of finitely generated indecomposable right
modules.  Both properties are transported along the proved ring isomorphism from `R_N` to the
matrix ring `R = (H T; 0 T)` of the manuscript.
-/

namespace QuantumFlags
noncomputable section
universe v

theorem actualCounterexample_right_rank_one :
    Module.finrank ActualCounterexampleBimodule.RightRingᵐᵒᵖ ActualCounterexampleBimodule.Space = 1 :=
  Module.finrank_eq_of_rank_eq (ambient_right_rank_one (actualFlagSystem.H 1))

/-- The matrix ring `R = (H T; 0 T)` of the manuscript for the actual extension `H ⊆ T`. -/
abbrev ActualTriangularRing := TriangularRing (actualFlagSystem.H 1)

theorem actual_bimodule_triangular_right_pure_semisimple :
    IsRightPureSemisimple.{0,v} (BimoduleTriangularRing ActualCounterexampleBimodule) :=
  triangular_right_pure_semisimple.{0,v} actualReflectionChain actualCounterexample_right_rank_one

/-- The actual matrix ring `R = (H T; 0 T)` is right pure semisimple. -/
theorem actual_triangular_right_pure_semisimple :
    IsRightPureSemisimple.{0,v} ActualTriangularRing :=
  everyModuleDirectSumFG_of_ringEquiv
    (RingEquiv.op (ambientTriangularRingEquiv (actualFlagSystem.H 1)))
    actual_bimodule_triangular_right_pure_semisimple

/-- The actual matrix ring `R = (H T; 0 T)` has infinitely many isomorphism classes of finitely
generated indecomposable right modules. -/
theorem actual_triangular_not_finitelyManyRightIndecomposables :
    ¬ FinitelyManyIndecomposables.{0,v} ActualTriangularRingᵐᵒᵖ := fun h =>
  triangular_not_finitelyManyIndecomposables.{0,v} actualReflectionChain
    actualCounterexample_right_rank_one
    (finitelyManyIndecomposables_of_ringEquiv
      (RingEquiv.op (ambientTriangularRingEquiv (actualFlagSystem.H 1))) h)

/-- The actual matrix ring `R = (H T; 0 T)` is not of finite representation type. -/
theorem actual_triangular_not_finite_representation_type :
    ¬ IsFiniteRepresentationType.{0,v} ActualTriangularRing := fun h =>
  actual_triangular_not_finitelyManyRightIndecomposables h.1

end
end QuantumFlags

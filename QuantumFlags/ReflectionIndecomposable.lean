import QuantumFlags.HomBiproducts
import QuantumFlags.EquivalenceIndecomposable

namespace QuantumFlags
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
variable (N : DivisionBimodule.{u}) [FiniteDimensional N.RightRingᵐᵒᵖ N.Space]

instance surjectiveDualTensorHasBinaryProducts :
    HasBinaryProducts (SurjectiveDualTensorObjects.{u,v} N) :=
  Adjunction.hasLimitsOfShape_of_equivalence (reflectionEquivalence N).inverse

instance surjectiveDualTensorHasBinaryBiproducts :
    HasBinaryBiproducts (SurjectiveDualTensorObjects.{u,v} N) :=
  HasBinaryBiproducts.of_hasBinaryProducts

theorem reflection_indecomposable_iff (M : InjectiveHomObjects.{u,v} N) :
    Indecomposable ((reflectionFunctor N).obj M) ↔ Indecomposable M :=
  equivalence_indecomposable_iff (reflectionEquivalence N) M

theorem inverseReflection_indecomposable_iff (L : SurjectiveDualTensorObjects.{u,v} N) :
    Indecomposable ((inverseReflectionFunctor N).obj L) ↔ Indecomposable L :=
  equivalence_indecomposable_iff (reflectionEquivalence N).symm L

end
end QuantumFlags

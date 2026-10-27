import QuantumFlags.ReflectionEquivalence
import QuantumFlags.RepresentationMorphismAddition
import Mathlib.CategoryTheory.Preadditive.Basic

namespace QuantumFlags
noncomputable section
open CategoryTheory
universe u v
variable (N : DivisionBimodule.{u})
local instance reflectionPreadditiveDualModule : Module N.LeftRingᵐᵒᵖ (RightDualSpace N) := dualRightModule N
local instance reflectionPreadditiveSourceModule (L : TensorRepresentation (rightDual N)) :
    Module N.RightRingᵐᵒᵖ L.Source := L.sourceModule
local instance reflectionPreadditiveTargetModule (L : TensorRepresentation (rightDual N)) :
    Module N.LeftRingᵐᵒᵖ L.Target := L.targetModule

instance injectiveHomPreadditive : Preadditive (InjectiveHomObjects.{u,v} N) where
  homGroup M P := HomRepresentationMorphism.addCommGroup M.val P.val
  add_comp M P Q f g h := by
    apply HomRepresentationMorphism.ext
    · apply LinearMap.ext
      intro x
      exact h.source.map_add _ _
    · apply LinearMap.ext
      intro y
      exact h.target.map_add _ _
  comp_add M P Q f g h := by
    apply HomRepresentationMorphism.ext <;> rfl

instance surjectiveDualTensorPreadditive : Preadditive (SurjectiveDualTensorObjects.{u,v} N) where
  homGroup L K := TensorRepresentationMorphism.addCommGroup L.val K.val
  add_comp L K J f g h := by
    apply TensorRepresentationMorphism.ext
    · apply LinearMap.ext
      intro x
      exact h.source.map_add _ _
    · apply LinearMap.ext
      intro y
      exact h.target.map_add _ _
  comp_add L K J f g h := by
    apply TensorRepresentationMorphism.ext <;> rfl

end
end QuantumFlags

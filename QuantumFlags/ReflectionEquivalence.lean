import QuantumFlags.ReflectionFunctorLaws
import Mathlib.CategoryTheory.Equivalence

namespace QuantumFlags
noncomputable section
open CategoryTheory
universe u v
variable (N : DivisionBimodule.{u}) [FiniteDimensional N.RightRingᵐᵒᵖ N.Space]
local instance reflectionEquivalenceDualModule : Module N.LeftRingᵐᵒᵖ (RightDualSpace N) := dualRightModule N
local instance reflectionEquivalenceHomModule (Y : Type*) [AddCommGroup Y] [Module N.RightRingᵐᵒᵖ Y] :
    Module N.LeftRingᵐᵒᵖ (BimoduleRightHom N Y) := rightHomModule N Y
local instance reflectionEquivalenceSourceModule (L : TensorRepresentation (rightDual N)) : Module N.RightRingᵐᵒᵖ L.Source :=
  L.sourceModule
local instance reflectionEquivalenceTargetModule (L : TensorRepresentation (rightDual N)) : Module N.LeftRingᵐᵒᵖ L.Target :=
  L.targetModule

abbrev InjectiveHomObjects :=
  {M : HomRepresentation.{u, max u v, max u v} N // Function.Injective M.arrow}

abbrev SurjectiveDualTensorObjects :=
  {L : TensorRepresentation.{u, max u v, max u v} (rightDual N) // Function.Surjective L.arrow}

instance injectiveHomCategory : Category (InjectiveHomObjects.{u,v} N) where
  Hom M P := HomRepresentationMorphism M.val P.val
  id M := HomRepresentationMorphism.identity M.val
  comp f g := HomRepresentationMorphism.compose g f
  id_comp f := HomRepresentationMorphism.compose_identity f
  comp_id f := HomRepresentationMorphism.identity_compose f
  assoc f g h := (HomRepresentationMorphism.compose_assoc h g f).symm

instance surjectiveDualTensorCategory : Category (SurjectiveDualTensorObjects.{u,v} N) where
  Hom L K := TensorRepresentationMorphism L.val K.val
  id L := TensorRepresentationMorphism.identity L.val
  comp f g := TensorRepresentationMorphism.compose g f
  id_comp f := TensorRepresentationMorphism.compose_identity f
  comp_id f := TensorRepresentationMorphism.identity_compose f
  assoc f g h := (TensorRepresentationMorphism.compose_assoc h g f).symm

def reflectionFunctor : InjectiveHomObjects.{u,v} N ⥤ SurjectiveDualTensorObjects.{u,v} N where
  obj M := ⟨reflectionForward N M.val, reflectionForward_surjective N M.val⟩
  map f := reflectionForwardMap N f
  map_id M := reflectionForwardMap_identity N M.val
  map_comp f g := reflectionForwardMap_comp N g f

def inverseReflectionFunctor : SurjectiveDualTensorObjects.{u,v} N ⥤ InjectiveHomObjects.{u,v} N where
  obj L := ⟨reflectionBackward N L.val, reflectionBackward_injective N L.val⟩
  map f := reflectionBackwardMap N f
  map_id L := reflectionBackwardMap_identity N L.val
  map_comp f g := reflectionBackwardMap_comp N g f

def reflectionUnitIso :
    𝟭 (InjectiveHomObjects.{u,v} N) ≅ reflectionFunctor N ⋙ inverseReflectionFunctor N :=
  NatIso.ofComponents (fun M => {
    hom := reflectionUnit N M.val
    inv := reflectionUnitInverse N M.val M.property
    hom_inv_id := reflectionUnit_left_inverse N M.val M.property
    inv_hom_id := reflectionUnit_right_inverse N M.val M.property })
    (by intro M P f; exact (reflectionUnit_natural N M.val f).symm)

def reflectionCounitIso :
    inverseReflectionFunctor N ⋙ reflectionFunctor N ≅ 𝟭 (SurjectiveDualTensorObjects.{u,v} N) :=
  NatIso.ofComponents (fun L => {
    hom := reflectionCounit N L.val
    inv := reflectionCounitInverse N L.val L.property
    hom_inv_id := reflectionCounit_left_inverse N L.val L.property
    inv_hom_id := reflectionCounit_right_inverse N L.val L.property })
    (by intro L K f; exact (reflectionCounit_natural N f).symm)

/-- The actual kernel-cokernel reflection equivalence on the injective/surjective subcategories. -/
def reflectionEquivalence : InjectiveHomObjects.{u,v} N ≌ SurjectiveDualTensorObjects.{u,v} N :=
  CategoryTheory.Equivalence.mk (reflectionFunctor N) (inverseReflectionFunctor N)
    (reflectionUnitIso N) (reflectionCounitIso N)

theorem reflection_equivalence_exists :
    Nonempty (InjectiveHomObjects.{u,v} N ≌ SurjectiveDualTensorObjects.{u,v} N) :=
  ⟨reflectionEquivalence N⟩

def reflectionHomEquiv (M P : InjectiveHomObjects.{u,v} N) :
    (M ⟶ P) ≃ ((reflectionFunctor N).obj M ⟶ (reflectionFunctor N).obj P) :=
  (reflectionEquivalence N).fullyFaithfulFunctor.homEquiv

theorem reflectionFunctor_map_bijective (M P : InjectiveHomObjects.{u,v} N) :
    Function.Bijective ((reflectionFunctor N).map :
      (M ⟶ P) → ((reflectionFunctor N).obj M ⟶ (reflectionFunctor N).obj P)) :=
  (reflectionEquivalence N).fullyFaithfulFunctor.map_bijective M P

end
end QuantumFlags

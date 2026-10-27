import QuantumFlags.HomRepresentationCategory
import QuantumFlags.EquivalenceIndecomposable

namespace QuantumFlags
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
variable (N : DivisionBimodule.{u})
local instance tensorCategoryHomModule (Y : Type*) [AddCommGroup Y]
    [Module N.RightRingᵐᵒᵖ Y] : Module N.LeftRingᵐᵒᵖ (BimoduleRightHom N Y) := rightHomModule N Y

instance tensorRepresentationCategory : Category (TensorRepresentation.{u, max u v, max u v} N) where
  Hom M P := TensorRepresentationMorphism M P
  id M := TensorRepresentationMorphism.identity M
  comp f g := TensorRepresentationMorphism.compose g f
  id_comp f := TensorRepresentationMorphism.compose_identity f
  comp_id f := TensorRepresentationMorphism.identity_compose f
  assoc f g h := (TensorRepresentationMorphism.compose_assoc h g f).symm

instance tensorRepresentationPreadditive :
    Preadditive (TensorRepresentation.{u, max u v, max u v} N) where
  homGroup M P := TensorRepresentationMorphism.addCommGroup M P
  add_comp M P Q f g h := by
    apply TensorRepresentationMorphism.ext
    · apply LinearMap.ext
      intro x
      exact h.source.map_add _ _
    · apply LinearMap.ext
      intro y
      exact h.target.map_add _ _
  comp_add M P Q f g h := by
    apply TensorRepresentationMorphism.ext <;> rfl

def tensorToHomFunctor : TensorRepresentation.{u, max u v, max u v} N ⥤
    HomRepresentation.{u, max u v, max u v} N where
  obj := tensorRepresentationToHom
  map := tensorMorphismToHom
  map_id := tensorMorphismToHom_identity
  map_comp f g := tensorMorphismToHom_comp g f

def homToTensorFunctor : HomRepresentation.{u, max u v, max u v} N ⥤
    TensorRepresentation.{u, max u v, max u v} N where
  obj := homRepresentationToTensor
  map := homMorphismToTensor
  map_id M := by apply TensorRepresentationMorphism.ext <;> rfl
  map_comp f g := by apply TensorRepresentationMorphism.ext <;> rfl

def tensorHomUnitIso : 𝟭 (TensorRepresentation.{u, max u v, max u v} N) ≅
    tensorToHomFunctor N ⋙ homToTensorFunctor N :=
  NatIso.ofComponents (fun M => {
    hom := {
      source := LinearMap.id
      target := LinearMap.id
      commutes z := by
        change (homRepresentationToTensor (tensorRepresentationToHom M)).arrow
          (balancedTensorMap N M.Source LinearMap.id z) = M.arrow z
        rw [balancedTensorMap_identity, tensorHom_arrow_roundtrip]
        rfl }
    inv := {
      source := LinearMap.id
      target := LinearMap.id
      commutes z := by
        change M.arrow (balancedTensorMap N M.Source LinearMap.id z) =
          (homRepresentationToTensor (tensorRepresentationToHom M)).arrow z
        rw [balancedTensorMap_identity, tensorHom_arrow_roundtrip]
        rfl }
    hom_inv_id := by apply TensorRepresentationMorphism.ext <;> rfl
    inv_hom_id := by apply TensorRepresentationMorphism.ext <;> rfl })
    (by intro M P f; apply TensorRepresentationMorphism.ext <;> rfl)

def tensorHomCounitIso : homToTensorFunctor N ⋙ tensorToHomFunctor N ≅
    𝟭 (HomRepresentation.{u, max u v, max u v} N) :=
  NatIso.ofComponents (fun M => {
    hom := {
      source := LinearMap.id
      target := LinearMap.id
      commutes x := by
        change M.arrow x = LinearMap.id.comp
          ((tensorRepresentationToHom (homRepresentationToTensor M)).arrow x)
        rw [LinearMap.id_comp, homTensor_arrow_roundtrip] }
    inv := {
      source := LinearMap.id
      target := LinearMap.id
      commutes x := by
        change (tensorRepresentationToHom (homRepresentationToTensor M)).arrow x =
          LinearMap.id.comp (M.arrow x)
        rw [LinearMap.id_comp, homTensor_arrow_roundtrip] }
    hom_inv_id := by apply HomRepresentationMorphism.ext <;> rfl
    inv_hom_id := by apply HomRepresentationMorphism.ext <;> rfl })
    (by intro M P f; apply HomRepresentationMorphism.ext <;> rfl)

def tensorHomCategoryEquivalence : TensorRepresentation.{u, max u v, max u v} N ≌
    HomRepresentation.{u, max u v, max u v} N :=
  CategoryTheory.Equivalence.mk (tensorToHomFunctor N) (homToTensorFunctor N)
    (tensorHomUnitIso N) (tensorHomCounitIso N)

theorem tensorHomCategoryEquivalence_exists :
    Nonempty (TensorRepresentation.{u, max u v, max u v} N ≌
      HomRepresentation.{u, max u v, max u v} N) :=
  ⟨tensorHomCategoryEquivalence N⟩

instance tensorRepresentationHasBinaryProducts :
    HasBinaryProducts (TensorRepresentation.{u, max u v, max u v} N) :=
  Adjunction.hasLimitsOfShape_of_equivalence (tensorHomCategoryEquivalence N).functor

instance tensorRepresentationHasBinaryBiproducts :
    HasBinaryBiproducts (TensorRepresentation.{u, max u v, max u v} N) :=
  HasBinaryBiproducts.of_hasBinaryProducts

end
end QuantumFlags

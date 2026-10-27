import QuantumFlags.RepresentationRetracts
import QuantumFlags.InverseReflectionEndRings

namespace QuantumFlags
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
variable (N : DivisionBimodule.{u})
local instance tensorReflectionHomModule (Y : Type*) [AddCommGroup Y]
    [Module N.RightRingᵐᵒᵖ Y] : Module N.LeftRingᵐᵒᵖ (BimoduleRightHom N Y) := rightHomModule N Y

abbrev InjectiveTensorObjects :=
  {M : TensorRepresentation.{u, max u v, max u v} N //
    Function.Injective (tensorRepresentationToHom M).arrow}

instance injectiveTensorCategory : Category (InjectiveTensorObjects.{u,v} N) where
  Hom M P := TensorRepresentationMorphism M.val P.val
  id M := TensorRepresentationMorphism.identity M.val
  comp f g := TensorRepresentationMorphism.compose g f
  id_comp f := TensorRepresentationMorphism.compose_identity f
  comp_id f := TensorRepresentationMorphism.identity_compose f
  assoc f g h := (TensorRepresentationMorphism.compose_assoc h g f).symm

def injectiveTensorToHom : InjectiveTensorObjects.{u,v} N ⥤ InjectiveHomObjects.{u,v} N where
  obj M := ⟨tensorRepresentationToHom M.val, M.property⟩
  map := tensorMorphismToHom
  map_id M := tensorMorphismToHom_identity M.val
  map_comp f g := tensorMorphismToHom_comp g f

def injectiveHomToTensor : InjectiveHomObjects.{u,v} N ⥤ InjectiveTensorObjects.{u,v} N where
  obj M := ⟨homRepresentationToTensor M.val, by
    change Function.Injective (tensorRepresentationToHom (homRepresentationToTensor M.val)).arrow
    rw [homTensor_arrow_roundtrip]
    exact M.property⟩
  map := homMorphismToTensor
  map_id M := by apply TensorRepresentationMorphism.ext <;> rfl
  map_comp f g := by apply TensorRepresentationMorphism.ext <;> rfl

def injectiveTensorHomUnitIso : 𝟭 (InjectiveTensorObjects.{u,v} N) ≅
    injectiveTensorToHom N ⋙ injectiveHomToTensor N :=
  NatIso.ofComponents (fun M => {
    hom := (tensorHomUnitIso N).hom.app M.val
    inv := (tensorHomUnitIso N).inv.app M.val
    hom_inv_id := (tensorHomUnitIso N).hom_inv_id_app M.val
    inv_hom_id := (tensorHomUnitIso N).inv_hom_id_app M.val })
    (by intro M P f; apply TensorRepresentationMorphism.ext <;> rfl)

def injectiveTensorHomCounitIso : injectiveHomToTensor N ⋙ injectiveTensorToHom N ≅
    𝟭 (InjectiveHomObjects.{u,v} N) :=
  NatIso.ofComponents (fun M => {
    hom := (tensorHomCounitIso N).hom.app M.val
    inv := (tensorHomCounitIso N).inv.app M.val
    hom_inv_id := (tensorHomCounitIso N).hom_inv_id_app M.val
    inv_hom_id := (tensorHomCounitIso N).inv_hom_id_app M.val })
    (by intro M P f; apply HomRepresentationMorphism.ext <;> rfl)

def injectiveTensorHomEquivalence : InjectiveTensorObjects.{u,v} N ≌ InjectiveHomObjects.{u,v} N :=
  CategoryTheory.Equivalence.mk (injectiveTensorToHom N) (injectiveHomToTensor N)
    (injectiveTensorHomUnitIso N) (injectiveTensorHomCounitIso N)

def tensorHomEndRingEquiv (M : TensorRepresentation.{u, max u v, max u v} N) :
    End M ≃+* End (tensorRepresentationToHom M) where
  toEquiv := (tensorHomCategoryEquivalence N).fullyFaithfulFunctor.homEquiv
  map_mul' f g := by apply HomRepresentationMorphism.ext <;> rfl
  map_add' f g := by apply HomRepresentationMorphism.ext <;> rfl

variable [FiniteDimensional N.RightRingᵐᵒᵖ N.Space]

/-- Reflection on the tensor representations appearing in the manuscript. -/
def tensorReflectionEquivalence :
    InjectiveTensorObjects.{u,v} N ≌ SurjectiveDualTensorObjects.{u,v} N :=
  (injectiveTensorHomEquivalence N).trans (reflectionEquivalence N)

theorem tensorReflectionEquivalence_exists :
    Nonempty (InjectiveTensorObjects.{u,v} N ≌ SurjectiveDualTensorObjects.{u,v} N) :=
  ⟨tensorReflectionEquivalence N⟩

theorem tensorReflection_object (M : InjectiveTensorObjects.{u,v} N) :
    ((tensorReflectionEquivalence N).functor.obj M).val =
      reflectionForward N (tensorRepresentationToHom M.val) := rfl

theorem inverseTensorReflection_object (L : SurjectiveDualTensorObjects.{u,v} N) :
    ((tensorReflectionEquivalence N).inverse.obj L).val =
      homRepresentationToTensor (reflectionBackward N L.val) := rfl

theorem tensorReflection_ambient_indecomposable_iff (M : InjectiveTensorObjects.{u,v} N) :
    Indecomposable (reflectionForward N (tensorRepresentationToHom M.val)) ↔
      Indecomposable M.val :=
  (reflection_ambient_indecomposable_iff N ((injectiveTensorToHom N).obj M)).trans
    (equivalence_indecomposable_iff (tensorHomCategoryEquivalence N) M.val)

theorem inverseTensorReflection_ambient_indecomposable_iff (L : SurjectiveDualTensorObjects.{u,v} N) :
    Indecomposable (homRepresentationToTensor (reflectionBackward N L.val)) ↔
      Indecomposable L.val :=
  (equivalence_indecomposable_iff (tensorHomCategoryEquivalence N).symm
    (reflectionBackward N L.val)).trans (inverseReflection_ambient_indecomposable_iff N L)

def tensorReflectionEndRingEquiv (M : InjectiveTensorObjects.{u,v} N) :
    End M.val ≃+* End (reflectionForward N (tensorRepresentationToHom M.val)) :=
  (tensorHomEndRingEquiv N M.val).trans
    (reflectionEndRingEquiv N ((injectiveTensorToHom N).obj M))

theorem tensorReflectionEndRingEquiv_exists (M : InjectiveTensorObjects.{u,v} N) :
    Nonempty (End M.val ≃+* End (reflectionForward N (tensorRepresentationToHom M.val))) :=
  ⟨tensorReflectionEndRingEquiv N M⟩

def inverseTensorReflectionEndRingEquiv (L : SurjectiveDualTensorObjects.{u,v} N) :
    End L.val ≃+* End (homRepresentationToTensor (reflectionBackward N L.val)) :=
  (inverseReflectionEndRingEquiv N L).trans
    ((isoEndRingEquiv ((tensorHomCounitIso N).app (reflectionBackward N L.val))).symm.trans
      (tensorHomEndRingEquiv N (homRepresentationToTensor (reflectionBackward N L.val))).symm)

theorem inverseTensorReflectionEndRingEquiv_exists (L : SurjectiveDualTensorObjects.{u,v} N) :
    Nonempty (End L.val ≃+* End (homRepresentationToTensor (reflectionBackward N L.val))) :=
  ⟨inverseTensorReflectionEndRingEquiv N L⟩

end
end QuantumFlags

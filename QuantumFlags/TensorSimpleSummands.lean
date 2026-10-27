import QuantumFlags.SimpleSummands
import QuantumFlags.TensorHomMorphismEquivalence

namespace QuantumFlags
noncomputable section
universe u v
variable (N : DivisionBimodule.{u})

abbrev tensorSimpleSource : TensorRepresentation.{u,max u v,max u v} N where
  Source := ULift.{v} N.LeftRingᵐᵒᵖ
  Target := PUnit.{max u v + 1}
  arrow := 0

abbrev tensorSimpleTarget : TensorRepresentation.{u,max u v,max u v} N where
  Source := PUnit.{max u v + 1}
  Target := ULift.{v} N.RightRingᵐᵒᵖ
  arrow := 0

theorem tensorSimpleSource_toHom :
    tensorRepresentationToHom (tensorSimpleSource.{u,v} N) = simpleSource.{u,v} N := rfl

theorem tensorSimpleTarget_toHom :
    tensorRepresentationToHom (tensorSimpleTarget.{u,v} N) = simpleTarget.{u,v} N := rfl

theorem tensorRepresentation_retraction_iff {S L : TensorRepresentation N} :
    (∃ (i : TensorRepresentationMorphism S L) (p : TensorRepresentationMorphism L S),
      TensorRepresentationMorphism.compose p i = TensorRepresentationMorphism.identity S) ↔
    (∃ (i : HomRepresentationMorphism (tensorRepresentationToHom S) (tensorRepresentationToHom L))
      (p : HomRepresentationMorphism (tensorRepresentationToHom L) (tensorRepresentationToHom S)),
      HomRepresentationMorphism.compose p i = HomRepresentationMorphism.identity (tensorRepresentationToHom S)) := by
  constructor
  · rintro ⟨i,p,h⟩
    refine ⟨tensorMorphismToHom i,tensorMorphismToHom p,?_⟩
    have he := congrArg tensorMorphismToHom h
    rw [tensorMorphismToHom_comp,tensorMorphismToHom_identity] at he
    exact he
  · rintro ⟨i,p,h⟩
    let ii : TensorRepresentationMorphism S L := tensorHomMorphismEquiv.symm i
    let pp : TensorRepresentationMorphism L S := tensorHomMorphismEquiv.symm p
    refine ⟨ii,pp,?_⟩
    apply (tensorHomMorphismEquiv (M := S) (P := S)).injective
    change tensorMorphismToHom (TensorRepresentationMorphism.compose pp ii) =
      tensorMorphismToHom (TensorRepresentationMorphism.identity S)
    rw [tensorMorphismToHom_comp,tensorMorphismToHom_identity]
    have hi : tensorMorphismToHom ii = i := tensorHomMorphismEquiv.apply_symm_apply i
    have hp : tensorMorphismToHom pp = p := tensorHomMorphismEquiv.apply_symm_apply p
    rw [hi,hp]
    exact h

variable (L : TensorRepresentation.{u,max u v,max u v} N)

def HasTensorSimpleSourceSummand : Prop :=
  ∃ (i : TensorRepresentationMorphism (tensorSimpleSource.{u,v} N) L)
    (p : TensorRepresentationMorphism L (tensorSimpleSource.{u,v} N)),
    TensorRepresentationMorphism.compose p i = TensorRepresentationMorphism.identity (tensorSimpleSource N)

def HasTensorSimpleTargetSummand : Prop :=
  ∃ (i : TensorRepresentationMorphism (tensorSimpleTarget.{u,v} N) L)
    (p : TensorRepresentationMorphism L (tensorSimpleTarget.{u,v} N)),
    TensorRepresentationMorphism.compose p i = TensorRepresentationMorphism.identity (tensorSimpleTarget N)

theorem tensorSimpleSourceSummand_iff_hom :
    HasTensorSimpleSourceSummand N L ↔ HasSimpleSourceSummand N (tensorRepresentationToHom L) :=
  tensorRepresentation_retraction_iff N

theorem tensorSimpleTargetSummand_iff_hom :
    HasTensorSimpleTargetSummand N L ↔ HasSimpleTargetSummand N (tensorRepresentationToHom L) :=
  tensorRepresentation_retraction_iff N

theorem no_tensorSimpleSourceSummand_iff_injective :
    ¬ HasTensorSimpleSourceSummand N L ↔
      Function.Injective (balancedTensorCurry N L.Source L.arrow) := by
  rw [tensorSimpleSourceSummand_iff_hom,no_simpleSourceSummand_tensor_iff_injective]

theorem no_tensorSimpleTargetSummand_iff_surjective :
    ¬ HasTensorSimpleTargetSummand N L ↔ Function.Surjective L.arrow := by
  rw [tensorSimpleTargetSummand_iff_hom,no_simpleTargetSummand_tensor_iff_surjective]

end
end QuantumFlags

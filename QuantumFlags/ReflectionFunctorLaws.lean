import QuantumFlags.ReflectionUnit
import QuantumFlags.ReflectionCounit

namespace QuantumFlags
noncomputable section
universe u v
variable (N : DivisionBimodule.{u}) [FiniteDimensional N.RightRingᵐᵒᵖ N.Space]
local instance reflectionFunctorLawsDualModule : Module N.LeftRingᵐᵒᵖ (RightDualSpace N) := dualRightModule N
local instance reflectionFunctorLawsHomModule (Y : Type*) [AddCommGroup Y] [Module N.RightRingᵐᵒᵖ Y] :
    Module N.LeftRingᵐᵒᵖ (BimoduleRightHom N Y) := rightHomModule N Y
local instance reflectionFunctorLawsSourceModule (L : TensorRepresentation (rightDual N)) : Module N.RightRingᵐᵒᵖ L.Source :=
  L.sourceModule
local instance reflectionFunctorLawsTargetModule (L : TensorRepresentation (rightDual N)) : Module N.LeftRingᵐᵒᵖ L.Target :=
  L.targetModule

theorem reflectionForwardMap_identity (M : HomRepresentation N) :
    reflectionForwardMap N (HomRepresentationMorphism.identity M) =
      TensorRepresentationMorphism.identity (reflectionForward N M) := by
  apply TensorRepresentationMorphism.ext
  · rfl
  · apply LinearMap.ext
    intro z
    obtain ⟨h,rfl⟩ := M.arrow.range.mkQ_surjective z
    change reflectionCokernelMap N (HomRepresentationMorphism.identity M) (M.arrow.range.mkQ h) =
      M.arrow.range.mkQ h
    rw [reflectionCokernelMap_mk]
    rfl

theorem reflectionForwardMap_comp {M P Q : HomRepresentation N}
    (g : HomRepresentationMorphism P Q) (f : HomRepresentationMorphism M P) :
    reflectionForwardMap N (HomRepresentationMorphism.compose g f) =
      TensorRepresentationMorphism.compose (reflectionForwardMap N g) (reflectionForwardMap N f) := by
  apply TensorRepresentationMorphism.ext
  · rfl
  · apply LinearMap.ext
    intro z
    obtain ⟨h,rfl⟩ := M.arrow.range.mkQ_surjective z
    change reflectionCokernelMap N (HomRepresentationMorphism.compose g f) (M.arrow.range.mkQ h) =
      reflectionCokernelMap N g (reflectionCokernelMap N f (M.arrow.range.mkQ h))
    simp only [reflectionCokernelMap_mk]
    rfl

theorem reflectionBackwardMap_identity (L : TensorRepresentation (rightDual N)) :
    reflectionBackwardMap N (TensorRepresentationMorphism.identity L) =
      HomRepresentationMorphism.identity (reflectionBackward N L) := by
  apply HomRepresentationMorphism.ext
  · apply LinearMap.ext
    intro z
    apply Subtype.ext
    change balancedTensorMap (rightDual N) L.Source LinearMap.id z.val = z.val
    rw [balancedTensorMap_identity]
    rfl
  · rfl

theorem reflectionBackwardMap_comp {L K J : TensorRepresentation (rightDual N)}
    (g : TensorRepresentationMorphism K J) (f : TensorRepresentationMorphism L K) :
    reflectionBackwardMap N (TensorRepresentationMorphism.compose g f) =
      HomRepresentationMorphism.compose (reflectionBackwardMap N g) (reflectionBackwardMap N f) := by
  apply HomRepresentationMorphism.ext
  · apply LinearMap.ext
    intro z
    apply Subtype.ext
    change balancedTensorMap (rightDual N) L.Source (g.source.comp f.source) z.val =
      balancedTensorMap (rightDual N) K.Source g.source
        (balancedTensorMap (rightDual N) L.Source f.source z.val)
    rw [balancedTensorMap_comp]
    rfl
  · rfl

theorem reflectionCounit_natural
    {L K : TensorRepresentation.{u, max u v, max u v} (rightDual N)}
    (f : TensorRepresentationMorphism L K) :
    TensorRepresentationMorphism.compose f (reflectionCounit N L) =
      TensorRepresentationMorphism.compose (reflectionCounit N K)
        (reflectionForwardMap N (reflectionBackwardMap N f)) := by
  apply TensorRepresentationMorphism.ext
  · rfl
  · apply LinearMap.ext
    intro z
    obtain ⟨h,rfl⟩ := (reflectionBackward N L).arrow.range.mkQ_surjective z
    change f.target (reflectionCounitTargetMap N L ((reflectionBackward N L).arrow.range.mkQ h)) =
      reflectionCounitTargetMap N K
        (reflectionCokernelMap N (reflectionBackwardMap N f) ((reflectionBackward N L).arrow.range.mkQ h))
    rw [reflectionCokernelMap_mk,reflectionCounitTargetMap_mk,reflectionCounitTargetMap_mk]
    have hn := LinearMap.congr_fun (dualTensorHomEquiv_natural N L.Source f.source)
      ((dualTensorHomEquiv N L.Source).symm h)
    change rightHomMap N f.source (dualTensorHomEquiv N L.Source
      ((dualTensorHomEquiv N L.Source).symm h)) =
      dualTensorHomEquiv N K.Source (balancedTensorMap (rightDual N) L.Source f.source
        ((dualTensorHomEquiv N L.Source).symm h)) at hn
    rw [LinearEquiv.apply_symm_apply] at hn
    have he : (dualTensorHomEquiv N K.Source).symm (rightHomMap N f.source h) =
        balancedTensorMap (rightDual N) L.Source f.source ((dualTensorHomEquiv N L.Source).symm h) := by
      apply (dualTensorHomEquiv N K.Source).injective
      rw [LinearEquiv.apply_symm_apply]
      exact hn
    change f.target (L.arrow ((dualTensorHomEquiv N L.Source).symm h)) =
      K.arrow ((dualTensorHomEquiv N K.Source).symm (rightHomMap N f.source h))
    rw [he]
    exact (f.commutes _).symm

end
end QuantumFlags

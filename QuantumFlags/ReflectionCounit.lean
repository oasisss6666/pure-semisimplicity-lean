import QuantumFlags.ReflectionObjects
import QuantumFlags.TensorRepresentationMaps

namespace QuantumFlags
noncomputable section
universe u v
variable (N : DivisionBimodule.{u}) [FiniteDimensional N.RightRingᵐᵒᵖ N.Space]
local instance reflectionCounitDualModule : Module N.LeftRingᵐᵒᵖ (RightDualSpace N) := dualRightModule N
local instance reflectionCounitHomModule (Y : Type*) [AddCommGroup Y] [Module N.RightRingᵐᵒᵖ Y] :
    Module N.LeftRingᵐᵒᵖ (BimoduleRightHom N Y) := rightHomModule N Y
local instance reflectionCounitSourceModule (L : TensorRepresentation (rightDual N)) : Module N.RightRingᵐᵒᵖ L.Source :=
  L.sourceModule
local instance reflectionCounitTargetModule (L : TensorRepresentation (rightDual N)) : Module N.LeftRingᵐᵒᵖ L.Target :=
  L.targetModule

variable (L : TensorRepresentation.{u, max u v, max u v} (rightDual N))

def reflectionCounitTargetMap :
    (reflectionForward N (reflectionBackward N L)).Target →ₗ[N.LeftRingᵐᵒᵖ] L.Target :=
  (reflectionBackward N L).arrow.range.liftQ
    (L.arrow.comp (dualTensorHomEquiv N L.Source).symm.toLinearMap) (by
      rintro z ⟨x,rfl⟩
      change L.arrow ((dualTensorHomEquiv N L.Source).symm
        (dualTensorHomEquiv N L.Source x.val)) = 0
      rw [LinearEquiv.symm_apply_apply]
      exact x.property)

theorem reflectionCounitTargetMap_mk (h : BimoduleRightHom N L.Source) :
    reflectionCounitTargetMap N L ((reflectionBackward N L).arrow.range.mkQ h) =
      L.arrow ((dualTensorHomEquiv N L.Source).symm h) := rfl

theorem reflectionCounitTargetMap_injective : Function.Injective (reflectionCounitTargetMap N L) := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm _ bot_le
  intro z hz
  obtain ⟨h,rfl⟩ := (reflectionBackward N L).arrow.range.mkQ_surjective z
  have hh : L.arrow ((dualTensorHomEquiv N L.Source).symm h) = 0 := hz
  change (reflectionBackward N L).arrow.range.mkQ h = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨⟨(dualTensorHomEquiv N L.Source).symm h,hh⟩, ?_⟩
  exact (dualTensorHomEquiv N L.Source).apply_symm_apply h

theorem reflectionCounitTargetMap_surjective (hL : Function.Surjective L.arrow) :
    Function.Surjective (reflectionCounitTargetMap N L) := by
  intro z
  obtain ⟨t,rfl⟩ := hL z
  refine ⟨(reflectionBackward N L).arrow.range.mkQ (dualTensorHomEquiv N L.Source t), ?_⟩
  rw [reflectionCounitTargetMap_mk,LinearEquiv.symm_apply_apply]

def reflectionCounitTargetEquiv (hL : Function.Surjective L.arrow) :
    (reflectionForward N (reflectionBackward N L)).Target ≃ₗ[N.LeftRingᵐᵒᵖ] L.Target :=
  LinearEquiv.ofBijective (reflectionCounitTargetMap N L)
    ⟨reflectionCounitTargetMap_injective N L,reflectionCounitTargetMap_surjective N L hL⟩

def reflectionCounit :
    TensorRepresentationMorphism (reflectionForward N (reflectionBackward N L)) L where
  source := LinearMap.id
  target := reflectionCounitTargetMap N L
  commutes z := by
    rw [balancedTensorMap_identity]
    change L.arrow z = reflectionCounitTargetMap N L
      ((reflectionBackward N L).arrow.range.mkQ (dualTensorHomEquiv N L.Source z))
    rw [reflectionCounitTargetMap_mk,LinearEquiv.symm_apply_apply]

def reflectionCounitInverse (hL : Function.Surjective L.arrow) :
    TensorRepresentationMorphism L (reflectionForward N (reflectionBackward N L)) where
  source := LinearMap.id
  target := (reflectionCounitTargetEquiv N L hL).symm.toLinearMap
  commutes z := by
    rw [balancedTensorMap_identity]
    apply (reflectionCounitTargetEquiv N L hL).injective
    change reflectionCounitTargetMap N L
      ((reflectionBackward N L).arrow.range.mkQ (dualTensorHomEquiv N L.Source z)) =
      reflectionCounitTargetEquiv N L hL ((reflectionCounitTargetEquiv N L hL).symm (L.arrow z))
    rw [reflectionCounitTargetMap_mk,LinearEquiv.symm_apply_apply,LinearEquiv.apply_symm_apply]

theorem reflectionCounit_left_inverse (hL : Function.Surjective L.arrow) :
    TensorRepresentationMorphism.compose (reflectionCounitInverse N L hL) (reflectionCounit N L) =
      TensorRepresentationMorphism.identity (reflectionForward N (reflectionBackward N L)) := by
  apply TensorRepresentationMorphism.ext
  · rfl
  · apply LinearMap.ext
    intro z
    exact (reflectionCounitTargetEquiv N L hL).symm_apply_apply z

theorem reflectionCounit_right_inverse (hL : Function.Surjective L.arrow) :
    TensorRepresentationMorphism.compose (reflectionCounit N L) (reflectionCounitInverse N L hL) =
      TensorRepresentationMorphism.identity L := by
  apply TensorRepresentationMorphism.ext
  · rfl
  · apply LinearMap.ext
    intro z
    exact (reflectionCounitTargetEquiv N L hL).apply_symm_apply z

end
end QuantumFlags

import QuantumFlags.FiniteDualTensor
import QuantumFlags.TensorRepresentations

namespace QuantumFlags
noncomputable section
universe u v

variable (N : DivisionBimodule.{u}) [FiniteDimensional N.RightRingᵐᵒᵖ N.Space]
local instance reflectionObjectsDualModule : Module N.LeftRingᵐᵒᵖ (RightDualSpace N) := dualRightModule N
local instance reflectionObjectsHomModule (Y : Type*) [AddCommGroup Y] [Module N.RightRingᵐᵒᵖ Y] :
    Module N.LeftRingᵐᵒᵖ (BimoduleRightHom N Y) := rightHomModule N Y

local instance reflectionObjectsSourceModule (L : TensorRepresentation (rightDual N)) : Module N.RightRingᵐᵒᵖ L.Source :=
  L.sourceModule
local instance reflectionObjectsTargetModule (L : TensorRepresentation (rightDual N)) : Module N.LeftRingᵐᵒᵖ L.Target :=
  L.targetModule

abbrev reflectionCokernel (M : HomRepresentation N) :=
  BimoduleRightHom N M.Target ⧸ M.arrow.range

abbrev reflectionForward (M : HomRepresentation N) : TensorRepresentation (rightDual N) where
  Source := M.Target
  Target := reflectionCokernel N M
  arrow := M.arrow.range.mkQ.comp (dualTensorHomEquiv N M.Target).toLinearMap

theorem reflectionForward_surjective (M : HomRepresentation N) :
    Function.Surjective (reflectionForward N M).arrow :=
  M.arrow.range.mkQ_surjective.comp (dualTensorHomEquiv N M.Target).surjective

abbrev reflectionBackward (L : TensorRepresentation (rightDual N)) : HomRepresentation N where
  Source := LinearMap.ker L.arrow
  Target := L.Source
  arrow := (dualTensorHomEquiv N L.Source).toLinearMap.comp (LinearMap.ker L.arrow).subtype

theorem reflectionBackward_injective (L : TensorRepresentation (rightDual N)) :
    Function.Injective (reflectionBackward N L).arrow :=
  (dualTensorHomEquiv N L.Source).injective.comp Subtype.val_injective

def reflectionCokernelMap {M P : HomRepresentation N}
    (f : HomRepresentationMorphism M P) :
    reflectionCokernel N M →ₗ[N.LeftRingᵐᵒᵖ] reflectionCokernel N P :=
  M.arrow.range.mapQ P.arrow.range (rightHomMap N f.target) (by
    rintro z ⟨x,rfl⟩
    exact ⟨f.source x, f.commutes x⟩)

theorem reflectionCokernelMap_mk {M P : HomRepresentation N}
    (f : HomRepresentationMorphism M P) (z : BimoduleRightHom N M.Target) :
    reflectionCokernelMap N f (M.arrow.range.mkQ z) =
      P.arrow.range.mkQ (rightHomMap N f.target z) := rfl

def reflectionForwardMap {M P : HomRepresentation N}
    (f : HomRepresentationMorphism M P) :
    TensorRepresentationMorphism (reflectionForward N M) (reflectionForward N P) where
  source := f.target
  target := reflectionCokernelMap N f
  commutes z := by
    change P.arrow.range.mkQ (dualTensorHomEquiv N P.Target
      (balancedTensorMap (rightDual N) M.Target f.target z)) =
      reflectionCokernelMap N f (M.arrow.range.mkQ (dualTensorHomEquiv N M.Target z))
    rw [reflectionCokernelMap_mk]
    have h := LinearMap.congr_fun (dualTensorHomEquiv_natural N M.Target f.target) z
    exact congrArg P.arrow.range.mkQ h.symm

def reflectionKernelMap {L K : TensorRepresentation (rightDual N)}
    (f : TensorRepresentationMorphism L K) :
    LinearMap.ker L.arrow →ₗ[N.LeftRingᵐᵒᵖ] LinearMap.ker K.arrow where
  toFun z := ⟨balancedTensorMap (rightDual N) L.Source f.source z.val, by
    change K.arrow (balancedTensorMap (rightDual N) L.Source f.source z.val) = 0
    rw [f.commutes, z.property, map_zero]⟩
  map_add' z w := Subtype.ext (map_add _ _ _)
  map_smul' a z := Subtype.ext (map_smul _ _ _)

def reflectionBackwardMap {L K : TensorRepresentation (rightDual N)}
    (f : TensorRepresentationMorphism L K) :
    HomRepresentationMorphism (reflectionBackward N L) (reflectionBackward N K) where
  source := reflectionKernelMap N f
  target := f.source
  commutes z := by
    change dualTensorHomEquiv N K.Source
      (balancedTensorMap (rightDual N) L.Source f.source z.val) =
      rightHomMap N f.source (dualTensorHomEquiv N L.Source z.val)
    have h := LinearMap.congr_fun (dualTensorHomEquiv_natural N L.Source f.source) z.val
    exact h.symm

end
end QuantumFlags

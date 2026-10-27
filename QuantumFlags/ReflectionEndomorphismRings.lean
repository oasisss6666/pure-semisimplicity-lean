import QuantumFlags.ReflectionPreadditive

namespace QuantumFlags
noncomputable section
open CategoryTheory
universe u v
variable (N : DivisionBimodule.{u}) [FiniteDimensional N.RightRingᵐᵒᵖ N.Space]
local instance reflectionEndomorphismHomModule (Y : Type*) [AddCommGroup Y] [Module N.RightRingᵐᵒᵖ Y] :
    Module N.LeftRingᵐᵒᵖ (BimoduleRightHom N Y) := rightHomModule N Y

local instance reflectionEndomorphismDualModule : Module N.LeftRingᵐᵒᵖ (RightDualSpace N) := dualRightModule N
local instance reflectionEndomorphismSourceModule (L : TensorRepresentation (rightDual N)) :
    Module N.RightRingᵐᵒᵖ L.Source := L.sourceModule
local instance reflectionEndomorphismTargetModule (L : TensorRepresentation (rightDual N)) :
    Module N.LeftRingᵐᵒᵖ L.Target := L.targetModule

variable (M : InjectiveHomObjects.{u,v} N)

theorem reflection_map_zero :
    (reflectionFunctor N).map (0 : M ⟶ M) = 0 := by
  apply TensorRepresentationMorphism.ext
  · rfl
  · apply LinearMap.ext
    intro z
    obtain ⟨h,rfl⟩ := M.val.arrow.range.mkQ_surjective z
    change reflectionCokernelMap N (0 : HomRepresentationMorphism M.val M.val)
      (M.val.arrow.range.mkQ h) = 0
    rw [reflectionCokernelMap_mk]
    change M.val.arrow.range.mkQ ((0 : M.val.Target →ₗ[N.RightRingᵐᵒᵖ] M.val.Target).comp h) = 0
    rw [LinearMap.zero_comp,map_zero]

theorem reflection_map_add (f g : End M) :
    (reflectionFunctor N).map (f+g) = (reflectionFunctor N).map f+(reflectionFunctor N).map g := by
  apply TensorRepresentationMorphism.ext
  · rfl
  · apply LinearMap.ext
    intro z
    obtain ⟨h,rfl⟩ := M.val.arrow.range.mkQ_surjective z
    change reflectionCokernelMap N (f+g) (M.val.arrow.range.mkQ h) =
      reflectionCokernelMap N f (M.val.arrow.range.mkQ h)+
        reflectionCokernelMap N g (M.val.arrow.range.mkQ h)
    simp only [reflectionCokernelMap_mk]
    change M.val.arrow.range.mkQ ((f.target+g.target).comp h) =
      M.val.arrow.range.mkQ (f.target.comp h)+M.val.arrow.range.mkQ (g.target.comp h)
    rw [LinearMap.add_comp,map_add]

def reflectionEndRingHom : End M →+* End ((reflectionFunctor N).obj M) where
  toFun := (reflectionFunctor N).map
  map_one' := (reflectionFunctor N).map_id M
  map_mul' f g := (reflectionFunctor N).map_comp g f
  map_zero' := reflection_map_zero N M
  map_add' := reflection_map_add N M

def reflectionEndRingEquiv : End M ≃+* End ((reflectionFunctor N).obj M) :=
  RingEquiv.ofBijective (reflectionEndRingHom N M) (reflectionFunctor_map_bijective N M M)

theorem reflectionEndRingEquiv_source (f : End M) :
    (reflectionEndRingEquiv N M f).source = f.target := rfl

theorem reflectionEndRingEquiv_exists :
    Nonempty (End M ≃+* End ((reflectionFunctor N).obj M)) :=
  ⟨reflectionEndRingEquiv N M⟩

end
end QuantumFlags

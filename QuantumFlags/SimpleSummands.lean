import QuantumFlags.ScalarLineRetractions
import QuantumFlags.TensorRepresentationMaps
import Mathlib.Algebra.Module.PUnit
import Mathlib.Algebra.Module.ULift

namespace QuantumFlags
noncomputable section
universe u v
variable (N : DivisionBimodule.{u})
local instance simpleSummandsHomModule (Y : Type*) [AddCommGroup Y] [Module N.RightRingᵐᵒᵖ Y] :
    Module N.LeftRingᵐᵒᵖ (BimoduleRightHom N Y) := rightHomModule N Y

abbrev simpleSource : HomRepresentation.{u,max u v,max u v} N where
  Source := ULift.{v} N.LeftRingᵐᵒᵖ
  Target := PUnit.{max u v + 1}
  arrow := 0

abbrev simpleTarget : HomRepresentation.{u,max u v,max u v} N where
  Source := PUnit.{max u v + 1}
  Target := ULift.{v} N.RightRingᵐᵒᵖ
  arrow := 0

variable (M : HomRepresentation.{u,max u v,max u v} N)

/-- A split copy of the canonical simple source representation. -/
def HasSimpleSourceSummand : Prop :=
  ∃ (i : HomRepresentationMorphism (simpleSource.{u,v} N) M)
    (p : HomRepresentationMorphism M (simpleSource.{u,v} N)),
    HomRepresentationMorphism.compose p i = HomRepresentationMorphism.identity (simpleSource N)

/-- A split copy of the canonical simple target representation. -/
def HasSimpleTargetSummand : Prop :=
  ∃ (i : HomRepresentationMorphism (simpleTarget.{u,v} N) M)
    (p : HomRepresentationMorphism M (simpleTarget.{u,v} N)),
    HomRepresentationMorphism.compose p i = HomRepresentationMorphism.identity (simpleTarget N)

theorem simpleSourceSummand_iff_kernelLine :
    HasSimpleSourceSummand N M ↔ HasKernelLine N.LeftRingᵐᵒᵖ M.arrow := by
  let e : ULift.{v} N.LeftRingᵐᵒᵖ ≃ₗ[N.LeftRingᵐᵒᵖ] N.LeftRingᵐᵒᵖ := ULift.moduleEquiv
  constructor
  · rintro ⟨i,p,hpi⟩
    refine ⟨i.source.comp e.symm.toLinearMap,e.toLinearMap.comp p.source,?_,?_⟩
    · apply LinearMap.ext
      intro a
      have h := LinearMap.congr_fun (congrArg HomRepresentationMorphism.source hpi) (e.symm a)
      change p.source (i.source (e.symm a)) = e.symm a at h
      change e (p.source (i.source (e.symm a))) = a
      rw [h,LinearEquiv.apply_symm_apply]
    · apply LinearMap.ext
      intro a
      have h := i.commutes (e.symm a)
      change M.arrow (i.source (e.symm a)) = i.target.comp 0 at h
      rw [LinearMap.comp_zero] at h
      exact h
  · rintro ⟨i,p,hpi,hfi⟩
    let ii : HomRepresentationMorphism (simpleSource.{u,v} N) M := {
      source := i.comp e.toLinearMap
      target := 0
      commutes x := by
        change M.arrow (i (e x)) = 0
        exact LinearMap.congr_fun hfi (e x) }
    let pp : HomRepresentationMorphism M (simpleSource.{u,v} N) := {
      source := e.symm.toLinearMap.comp p
      target := 0
      commutes x := by apply LinearMap.ext; intro n; rfl }
    refine ⟨ii,pp,?_⟩
    apply HomRepresentationMorphism.ext
    · apply LinearMap.ext
      intro x
      change e.symm (p (i (e x))) = x
      have h := LinearMap.congr_fun hpi (e x)
      change p (i (e x)) = e x at h
      rw [h,LinearEquiv.symm_apply_apply]
    · apply LinearMap.ext
      intro x
      exact Subsingleton.elim _ _

theorem simpleTargetSummand_iff_cokernelLine :
    HasSimpleTargetSummand N M ↔
      HasCokernelLine N.RightRingᵐᵒᵖ (homRepresentationToTensor M).arrow := by
  let e : ULift.{v} N.RightRingᵐᵒᵖ ≃ₗ[N.RightRingᵐᵒᵖ] N.RightRingᵐᵒᵖ := ULift.moduleEquiv
  constructor
  · rintro ⟨i,p,hpi⟩
    refine ⟨i.target.comp e.symm.toLinearMap,e.toLinearMap.comp p.target,?_,?_⟩
    · apply LinearMap.ext
      intro b
      have h := LinearMap.congr_fun (congrArg HomRepresentationMorphism.target hpi) (e.symm b)
      change p.target (i.target (e.symm b)) = e.symm b at h
      change e (p.target (i.target (e.symm b))) = b
      rw [h,LinearEquiv.apply_symm_apply]
    · apply balancedTensor_ext N M.Source
      intro x n
      change e (p.target ((homRepresentationToTensor M).arrow (balancedPure N M.Source x n))) = 0
      rw [homRepresentationToTensor_pure]
      have h := LinearMap.congr_fun (p.commutes x) n
      change 0 = p.target (M.arrow x n) at h
      rw [← h,map_zero]
  · rintro ⟨i,p,hpi,hpf⟩
    let ii : HomRepresentationMorphism (simpleTarget.{u,v} N) M := {
      source := 0
      target := i.comp e.toLinearMap
      commutes x := by
        change M.arrow 0 = (i.comp e.toLinearMap).comp 0
        rw [map_zero,LinearMap.comp_zero] }
    let pp : HomRepresentationMorphism M (simpleTarget.{u,v} N) := {
      source := 0
      target := e.symm.toLinearMap.comp p
      commutes x := by
        apply LinearMap.ext
        intro n
        change 0 = e.symm (p (M.arrow x n))
        have h := LinearMap.congr_fun hpf (balancedPure N M.Source x n)
        change p ((homRepresentationToTensor M).arrow (balancedPure N M.Source x n)) = 0 at h
        rw [homRepresentationToTensor_pure] at h
        rw [h,map_zero] }
    refine ⟨ii,pp,?_⟩
    apply HomRepresentationMorphism.ext
    · apply LinearMap.ext
      intro x
      exact Subsingleton.elim _ _
    · apply LinearMap.ext
      intro y
      change e.symm (p (i (e y))) = y
      have h := LinearMap.congr_fun hpi (e y)
      change p (i (e y)) = e y at h
      rw [h,LinearEquiv.symm_apply_apply]

theorem no_simpleSourceSummand_iff_injective :
    ¬ HasSimpleSourceSummand N M ↔ Function.Injective M.arrow := by
  rw [simpleSourceSummand_iff_kernelLine,hasKernelLine_iff_not_injective,not_not]

theorem no_simpleTargetSummand_iff_surjective :
    ¬ HasSimpleTargetSummand N M ↔ Function.Surjective (homRepresentationToTensor M).arrow := by
  rw [simpleTargetSummand_iff_cokernelLine,hasCokernelLine_iff_not_surjective,not_not]


theorem no_simpleSourceSummand_tensor_iff_injective
    (L : TensorRepresentation.{u,max u v,max u v} N) :
    ¬ HasSimpleSourceSummand N (tensorRepresentationToHom L) ↔
      Function.Injective (balancedTensorCurry N L.Source L.arrow) :=
  no_simpleSourceSummand_iff_injective N (tensorRepresentationToHom L)

theorem no_simpleTargetSummand_tensor_iff_surjective
    (L : TensorRepresentation.{u,max u v,max u v} N) :
    ¬ HasSimpleTargetSummand N (tensorRepresentationToHom L) ↔ Function.Surjective L.arrow := by
  rw [no_simpleTargetSummand_iff_surjective, tensorHom_arrow_roundtrip]

end
end QuantumFlags

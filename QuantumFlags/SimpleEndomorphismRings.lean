import QuantumFlags.HomRepresentationCategory
import QuantumFlags.SimpleSummands

namespace QuantumFlags
noncomputable section
open CategoryTheory
universe u v
variable (N : DivisionBimodule.{u})
local instance simpleEndHomModule (Y : Type*) [AddCommGroup Y]
    [Module N.RightRingᵐᵒᵖ Y] : Module N.LeftRingᵐᵒᵖ (BimoduleRightHom N Y) := rightHomModule N Y

def simpleSourceEndRingHom : End (simpleSource.{u,v} N) →+*
    Module.End N.LeftRingᵐᵒᵖ (ULift.{v} N.LeftRingᵐᵒᵖ) where
  toFun f := f.source
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

theorem simpleSourceEndRingHom_bijective : Function.Bijective (simpleSourceEndRingHom.{u,v} N) := by
  constructor
  · intro f g h
    apply HomRepresentationMorphism.ext h
    apply LinearMap.ext
    intro x
    exact Subsingleton.elim _ _
  · intro f
    refine ⟨{ source := f, target := 0, commutes := ?_ }, rfl⟩
    intro x
    change (0 : BimoduleRightHom N PUnit) = (0 : PUnit →ₗ[N.RightRingᵐᵒᵖ] PUnit).comp 0
    rw [LinearMap.comp_zero]

def simpleSourceEndRingEquiv : End (simpleSource.{u,v} N) ≃+* N.LeftRing :=
  (RingEquiv.ofBijective (simpleSourceEndRingHom N) (simpleSourceEndRingHom_bijective N)).trans
    ((ULift.moduleEquiv : ULift.{v} N.LeftRingᵐᵒᵖ ≃ₗ[N.LeftRingᵐᵒᵖ] N.LeftRingᵐᵒᵖ).conjRingEquiv.trans
      ((RingEquiv.moduleEndSelf N.LeftRingᵐᵒᵖ).symm.trans (RingEquiv.opOp N.LeftRing).symm))

theorem simpleSourceEndRingEquiv_exists : Nonempty (End (simpleSource.{u,v} N) ≃+* N.LeftRing) :=
  ⟨simpleSourceEndRingEquiv N⟩

def simpleTargetEndRingHom : End (simpleTarget.{u,v} N) →+*
    Module.End N.RightRingᵐᵒᵖ (ULift.{v} N.RightRingᵐᵒᵖ) where
  toFun f := f.target
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

theorem simpleTargetEndRingHom_bijective : Function.Bijective (simpleTargetEndRingHom.{u,v} N) := by
  constructor
  · intro f g h
    apply HomRepresentationMorphism.ext _ h
    apply LinearMap.ext
    intro x
    exact Subsingleton.elim _ _
  · intro f
    refine ⟨{ source := 0, target := f, commutes := ?_ }, rfl⟩
    intro x
    change (0 : BimoduleRightHom N (ULift.{v} N.RightRingᵐᵒᵖ)) = f.comp 0
    rw [LinearMap.comp_zero]

def simpleTargetEndRingEquiv : End (simpleTarget.{u,v} N) ≃+* N.RightRing :=
  (RingEquiv.ofBijective (simpleTargetEndRingHom N) (simpleTargetEndRingHom_bijective N)).trans
    ((ULift.moduleEquiv : ULift.{v} N.RightRingᵐᵒᵖ ≃ₗ[N.RightRingᵐᵒᵖ] N.RightRingᵐᵒᵖ).conjRingEquiv.trans
      ((RingEquiv.moduleEndSelf N.RightRingᵐᵒᵖ).symm.trans (RingEquiv.opOp N.RightRing).symm))

theorem simpleTargetEndRingEquiv_exists : Nonempty (End (simpleTarget.{u,v} N) ≃+* N.RightRing) :=
  ⟨simpleTargetEndRingEquiv N⟩

end
end QuantumFlags

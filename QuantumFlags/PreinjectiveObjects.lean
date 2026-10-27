import QuantumFlags.RepresentationIsoDimensions
import QuantumFlags.IndecomposableRepresentationArrows
import QuantumFlags.InverseReflectionDimensions

namespace QuantumFlags
noncomputable section
open CategoryTheory
universe u v

structure PreinjectiveObject (N : DivisionBimodule.{u}) (k : ℕ) where
  obj : TensorRepresentation.{u,max u v,max u v} N
  [sourceFinite : FiniteDimensional N.LeftRingᵐᵒᵖ obj.Source]
  [targetFinite : FiniteDimensional N.RightRingᵐᵒᵖ obj.Target]
  source_finrank : Module.finrank N.LeftRingᵐᵒᵖ obj.Source = k+1
  target_finrank : Module.finrank N.RightRingᵐᵒᵖ obj.Target = k
  arrow_surjective : Function.Surjective obj.arrow
  Scalar : Type u
  [scalarDivision : DivisionRing Scalar]
  endEquiv : End obj ≃+* Scalar

attribute [instance] PreinjectiveObject.sourceFinite PreinjectiveObject.targetFinite
  PreinjectiveObject.scalarDivision

variable (N : DivisionBimodule.{u})

theorem preinjectiveObject_indecomposable {k : ℕ} (L : PreinjectiveObject.{u,v} N k) :
    Indecomposable L.obj :=
  indecomposable_of_endRingEquiv_division _ L.endEquiv

def preinjectiveSimple : PreinjectiveObject.{u,v} N 0 where
  obj := tensorSimpleSource N
  source_finrank := simpleSource_source_finrank N
  target_finrank := simpleSource_target_finrank N
  arrow_surjective y := ⟨0, Subsingleton.elim _ _⟩
  Scalar := N.LeftRing
  endEquiv := tensorSimpleSourceEndRingEquiv N

variable [FiniteDimensional N.RightRingᵐᵒᵖ N.Space]
local instance preinjectiveDualModule : Module N.LeftRingᵐᵒᵖ (RightDualSpace N) := dualRightModule N
variable [FiniteDimensional N.LeftRingᵐᵒᵖ (RightDualSpace N)]
local instance preinjectiveSourceModule (L : TensorRepresentation (rightDual N)) :
    Module N.RightRingᵐᵒᵖ L.Source := L.sourceModule
local instance preinjectiveTargetModule (L : TensorRepresentation (rightDual N)) :
    Module N.LeftRingᵐᵒᵖ L.Target := L.targetModule

def preinjectiveBackward {k : ℕ}
    (hD : Module.finrank N.LeftRingᵐᵒᵖ (RightDualSpace N) = 2)
    (L : PreinjectiveObject.{u,v} (rightDual N) k) : PreinjectiveObject.{u,v} N (k+1) := by
  let S : SurjectiveDualTensorObjects.{u,v} N := ⟨L.obj, L.arrow_surjective⟩
  letI : FiniteDimensional N.RightRingᵐᵒᵖ L.obj.Source := L.sourceFinite
  letI : FiniteDimensional N.LeftRingᵐᵒᵖ L.obj.Target := L.targetFinite
  let M := homRepresentationToTensor (reflectionBackward N L.obj)
  letI : FiniteDimensional N.LeftRingᵐᵒᵖ M.Source := reflectionBackwardSourceFinite N L.obj
  letI : FiniteDimensional N.RightRingᵐᵒᵖ M.Target := reflectionBackwardTargetFinite N L.obj
  have hs : Module.finrank N.LeftRingᵐᵒᵖ M.Source = (k+1)+1 := by
    have h := reflectionBackward_source_finrank N L.obj L.arrow_surjective
    rw [hD, L.source_finrank, L.target_finrank] at h
    change Module.finrank N.LeftRingᵐᵒᵖ M.Source = 2*(k+1)-k at h
    omega
  have ht : Module.finrank N.RightRingᵐᵒᵖ M.Target = k+1 := L.source_finrank
  let e : End M ≃+* L.Scalar := (inverseTensorReflectionEndRingEquiv N S).symm.trans L.endEquiv
  have hi : Indecomposable M := indecomposable_of_endRingEquiv_division M e
  refine {
    obj := M
    source_finrank := hs
    target_finrank := ht
    arrow_surjective := indecomposable_tensorArrow_surjective N M hi ?_
    Scalar := L.Scalar
    endEquiv := e }
  exact positiveSource_not_simpleTarget (by rw [hs]; omega)

end
end QuantumFlags

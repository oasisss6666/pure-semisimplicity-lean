import QuantumFlags.SimpleEndomorphismRings
import QuantumFlags.EndRingIndecomposable
import QuantumFlags.TensorReflectionEquivalence

namespace QuantumFlags
noncomputable section
open CategoryTheory
universe u v
variable (N : DivisionBimodule.{u})
local instance projectiveHomModule (Y : Type*) [AddCommGroup Y]
    [Module N.RightRingᵐᵒᵖ Y] : Module N.LeftRingᵐᵒᵖ (BimoduleRightHom N Y) := rightHomModule N Y

abbrev canonicalProjective : HomRepresentation.{u,max u v,max u v} N where
  Source := ULift.{v} N.LeftRingᵐᵒᵖ
  Target := ULift.{v} N.Space
  arrow := {
    toFun x := {
      toFun n := ULift.up (x.down.unop • n)
      map_add' n m := by change ULift.up (x.down.unop • (n+m)) = _; rw [smul_add]; rfl
      map_smul' b n := by change ULift.up (x.down.unop • (b • n)) = _; rw [smul_comm]; rfl }
    map_add' x y := by
      apply LinearMap.ext; intro n
      change ULift.up ((x.down.unop+y.down.unop) • n) = _
      rw [add_smul]; rfl
    map_smul' a x := by
      apply LinearMap.ext; intro n
      change ULift.up ((x.down.unop*a.unop) • n) = ULift.up (x.down.unop • (a.unop • n))
      rw [mul_smul] }

theorem canonicalProjective_arrow (x : ULift.{v} N.LeftRingᵐᵒᵖ) (n : N.Space) :
    (canonicalProjective N).arrow x n = ULift.up (x.down.unop • n) := rfl

def canonicalProjectiveEndRingHom : End (canonicalProjective.{u,v} N) →+*
    Module.End N.LeftRingᵐᵒᵖ (ULift.{v} N.LeftRingᵐᵒᵖ) where
  toFun f := f.source
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

theorem canonicalProjectiveEnd_target (f : End (canonicalProjective.{u,v} N))
    (n : N.Space) :
    f.target (ULift.up n) =
      ULift.up ((f.source (ULift.up 1)).down.unop • n) := by
  have h := LinearMap.congr_fun (f.commutes (ULift.up 1)) n
  change ULift.up ((f.source (ULift.up 1)).down.unop • n) =
    f.target (ULift.up ((1 : N.LeftRing) • n)) at h
  simpa only [one_smul] using h.symm

def canonicalProjectiveEndLift
    (f : Module.End N.LeftRingᵐᵒᵖ (ULift.{v} N.LeftRingᵐᵒᵖ)) :
    End (canonicalProjective.{u,v} N) where
  source := f
  target := (ULift.moduleEquiv : ULift.{v} N.Space ≃ₗ[N.RightRingᵐᵒᵖ] N.Space).symm.toLinearMap.comp
    ((bimoduleLeftAction N (f (ULift.up 1)).down.unop).comp
      (ULift.moduleEquiv : ULift.{v} N.Space ≃ₗ[N.RightRingᵐᵒᵖ] N.Space).toLinearMap)
  commutes x := by
    apply LinearMap.ext; intro n
    have hx : f x = x.down • f (ULift.up 1) := by
      calc
        f x = f (x.down • ULift.up 1) := by congr 1; apply ULift.ext; exact (mul_one x.down).symm
        _ = x.down • f (ULift.up 1) := f.map_smul x.down (ULift.up 1)
    change ULift.up ((f x).down.unop • n) =
      ULift.up ((f (ULift.up 1)).down.unop • (x.down.unop • n))
    rw [hx]
    change ULift.up (((f (ULift.up 1)).down.unop * x.down.unop) • n) = _
    rw [mul_smul]

theorem canonicalProjectiveEndRingHom_bijective :
    Function.Bijective (canonicalProjectiveEndRingHom.{u,v} N) := by
  constructor
  · intro f g h
    apply HomRepresentationMorphism.ext h
    apply LinearMap.ext; intro n
    rcases n with ⟨n⟩
    rw [canonicalProjectiveEnd_target, canonicalProjectiveEnd_target]
    exact congrArg (fun k : Module.End N.LeftRingᵐᵒᵖ (ULift.{v} N.LeftRingᵐᵒᵖ) =>
      ULift.up ((k (ULift.up 1)).down.unop • n)) h
  · intro f
    exact ⟨canonicalProjectiveEndLift N f, rfl⟩

def canonicalProjectiveEndRingEquiv : End (canonicalProjective.{u,v} N) ≃+* N.LeftRing :=
  (RingEquiv.ofBijective (canonicalProjectiveEndRingHom N)
    (canonicalProjectiveEndRingHom_bijective N)).trans
    ((ULift.moduleEquiv : ULift.{v} N.LeftRingᵐᵒᵖ ≃ₗ[N.LeftRingᵐᵒᵖ] N.LeftRingᵐᵒᵖ).conjRingEquiv.trans
      ((RingEquiv.moduleEndSelf N.LeftRingᵐᵒᵖ).symm.trans (RingEquiv.opOp N.LeftRing).symm))

theorem canonicalProjectiveEndRingEquiv_exists :
    Nonempty (End (canonicalProjective.{u,v} N) ≃+* N.LeftRing) :=
  ⟨canonicalProjectiveEndRingEquiv N⟩

theorem canonicalProjective_indecomposable : Indecomposable (canonicalProjective.{u,v} N) :=
  indecomposable_of_endRingEquiv_division _ (canonicalProjectiveEndRingEquiv N)

abbrev tensorCanonicalProjective : TensorRepresentation.{u,max u v,max u v} N :=
  homRepresentationToTensor (canonicalProjective.{u,v} N)

def homTensorEndRingEquiv (M : HomRepresentation.{u,max u v,max u v} N) :
    End M ≃+* End (homRepresentationToTensor M) where
  toEquiv := (tensorHomCategoryEquivalence N).fullyFaithfulInverse.homEquiv
  map_mul' f g := by apply TensorRepresentationMorphism.ext <;> rfl
  map_add' f g := by apply TensorRepresentationMorphism.ext <;> rfl

def tensorCanonicalProjectiveEndRingEquiv :
    End (tensorCanonicalProjective.{u,v} N) ≃+* N.LeftRing :=
  (homTensorEndRingEquiv N (canonicalProjective N)).symm.trans (canonicalProjectiveEndRingEquiv N)

theorem tensorCanonicalProjective_indecomposable :
    Indecomposable (tensorCanonicalProjective.{u,v} N) :=
  indecomposable_of_endRingEquiv_division _ (tensorCanonicalProjectiveEndRingEquiv N)

end
end QuantumFlags

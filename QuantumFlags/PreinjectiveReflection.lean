import QuantumFlags.PreinjectiveFamily

namespace QuantumFlags
noncomputable section
open CategoryTheory
universe u v
variable {N : DivisionBimodule.{u}}

theorem preinjectiveFamily_zero_object (C : RightReflectionChain N) (r : ℕ) :
    (preinjectiveFamily.{u,v} C 0 r).obj = tensorSimpleSource (iteratedRightDual N r) := rfl

theorem preinjectiveFamily_successor_object (C : RightReflectionChain N) (k r : ℕ) :
    letI := C.finite r
    (preinjectiveFamily.{u,v} C (k+1) r).obj =
      homRepresentationToTensor (reflectionBackward (iteratedRightDual N r)
        (preinjectiveFamily C k (r+1)).obj) := rfl

def preinjectiveFamilyReflectionIso (C : RightReflectionChain N) (k r : ℕ) :
    letI := C.finite r
    reflectionForward (iteratedRightDual N r)
      (tensorRepresentationToHom (preinjectiveFamily.{u,v} C (k+1) r).obj) ≅
        (preinjectiveFamily C k (r+1)).obj := by
  letI := C.finite r
  let L : SurjectiveDualTensorObjects.{u,v} (iteratedRightDual N r) :=
    ⟨(preinjectiveFamily C k (r+1)).obj, (preinjectiveFamily C k (r+1)).arrow_surjective⟩
  let e := (tensorReflectionEquivalence (iteratedRightDual N r)).counitIso.app L
  exact {
    hom := e.hom
    inv := e.inv
    hom_inv_id := e.hom_inv_id
    inv_hom_id := e.inv_hom_id }

theorem preinjectiveFamilyReflectionIso_exists (C : RightReflectionChain N) (k r : ℕ) :
    letI := C.finite r
    Nonempty (reflectionForward (iteratedRightDual N r)
      (tensorRepresentationToHom (preinjectiveFamily.{u,v} C (k+1) r).obj) ≅
        (preinjectiveFamily C k (r+1)).obj) :=
  ⟨preinjectiveFamilyReflectionIso C k r⟩

end
end QuantumFlags

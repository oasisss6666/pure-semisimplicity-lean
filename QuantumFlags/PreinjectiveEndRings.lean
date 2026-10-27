import QuantumFlags.PreinjectiveFamily

namespace QuantumFlags
noncomputable section
open CategoryTheory
universe u v
variable {N : DivisionBimodule.{u}}

def preinjectiveFamilyEndRingEquiv (C : RightReflectionChain N) : (k r : ℕ) →
    End (preinjectiveFamily.{u,v} C k r).obj ≃+* (iteratedRightDual N (r+k)).LeftRing
  | 0, r => tensorSimpleSourceEndRingEquiv (iteratedRightDual N r)
  | k+1, r => by
    letI := C.finite r
    letI := dualRightModule (iteratedRightDual N r)
    letI : FiniteDimensional (iteratedRightDual N r).LeftRingᵐᵒᵖ
        (RightDualSpace (iteratedRightDual N r)) := C.finite (r+1)
    let S : SurjectiveDualTensorObjects.{u,v} (iteratedRightDual N r) :=
      ⟨(preinjectiveFamily C k (r+1)).obj, (preinjectiveFamily C k (r+1)).arrow_surjective⟩
    have h : r+(k+1) = (r+1)+k := by omega
    rw [h]
    exact (inverseTensorReflectionEndRingEquiv (iteratedRightDual N r) S).symm.trans
      (preinjectiveFamilyEndRingEquiv C k (r+1))

theorem preinjectiveFamilyEndRingEquiv_exists (C : RightReflectionChain N) (k r : ℕ) :
    Nonempty (End (preinjectiveFamily.{u,v} C k r).obj ≃+*
      (iteratedRightDual N (r+k)).LeftRing) :=
  ⟨preinjectiveFamilyEndRingEquiv C k r⟩

theorem preinjectiveRepresentationEndRingEquiv_exists (C : RightReflectionChain N) (k : ℕ) :
    Nonempty (End (preinjectiveRepresentation.{u,v} C k) ≃+*
      (iteratedRightDual N k).LeftRing) :=
  by
    have h := preinjectiveFamilyEndRingEquiv_exists.{u,v} C k 0
    rw [Nat.zero_add] at h
    exact h

end
end QuantumFlags

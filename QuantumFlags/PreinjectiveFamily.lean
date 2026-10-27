import QuantumFlags.PreinjectiveObjects

namespace QuantumFlags
noncomputable section
open CategoryTheory
universe u v

structure RightReflectionChain (N : DivisionBimodule.{u}) where
  finite : ∀ r : ℕ,
    FiniteDimensional (iteratedRightDual N r).RightRingᵐᵒᵖ (iteratedRightDual N r).Space
  double : ∀ r : ℕ,
    Module.finrank (iteratedRightDual N (r+1)).RightRingᵐᵒᵖ
      (iteratedRightDual N (r+1)).Space = 2

variable {N : DivisionBimodule.{u}}

def preinjectiveFamily (C : RightReflectionChain N) :
    (k r : ℕ) → PreinjectiveObject.{u,v} (iteratedRightDual N r) k
  | 0, r => preinjectiveSimple (iteratedRightDual N r)
  | k+1, r => by
    letI := C.finite r
    letI := dualRightModule (iteratedRightDual N r)
    letI : FiniteDimensional (iteratedRightDual N r).LeftRingᵐᵒᵖ
        (RightDualSpace (iteratedRightDual N r)) := C.finite (r+1)
    exact preinjectiveBackward (iteratedRightDual N r) (C.double r)
      (preinjectiveFamily C k (r+1))

abbrev preinjectiveRepresentation (C : RightReflectionChain N) (k : ℕ) :
    TensorRepresentation.{u,max u v,max u v} N := (preinjectiveFamily.{u,v} C k 0).obj

theorem preinjectiveFamily_dimension_vector (C : RightReflectionChain N) (k r : ℕ) :
    (Module.finrank (iteratedRightDual N r).LeftRingᵐᵒᵖ (preinjectiveFamily.{u,v} C k r).obj.Source,
      Module.finrank (iteratedRightDual N r).RightRingᵐᵒᵖ (preinjectiveFamily.{u,v} C k r).obj.Target) =
        (k+1,k) :=
  Prod.ext (preinjectiveFamily C k r).source_finrank (preinjectiveFamily C k r).target_finrank

theorem preinjectiveFamily_indecomposable (C : RightReflectionChain N) (k r : ℕ) :
    Indecomposable (preinjectiveFamily.{u,v} C k r).obj :=
  preinjectiveObject_indecomposable _ _

theorem preinjectiveFamily_arrow_surjective (C : RightReflectionChain N) (k r : ℕ) :
    Function.Surjective (preinjectiveFamily.{u,v} C k r).obj.arrow :=
  (preinjectiveFamily C k r).arrow_surjective

theorem preinjectiveFamily_endo_division (C : RightReflectionChain N) (k r : ℕ) :
    ∃ (K : Type u) (_ : DivisionRing K),
      Nonempty (End (preinjectiveFamily.{u,v} C k r).obj ≃+* K) :=
  ⟨(preinjectiveFamily C k r).Scalar, inferInstance, ⟨(preinjectiveFamily C k r).endEquiv⟩⟩

theorem preinjectiveRepresentation_dimension_vector (C : RightReflectionChain N) (k : ℕ) :
    (Module.finrank N.LeftRingᵐᵒᵖ (preinjectiveRepresentation.{u,v} C k).Source,
      Module.finrank N.RightRingᵐᵒᵖ (preinjectiveRepresentation.{u,v} C k).Target) = (k+1,k) :=
  preinjectiveFamily_dimension_vector C k 0

theorem preinjectiveRepresentation_pairwise_nonisomorphic
    (C : RightReflectionChain N) {k l : ℕ} (hkl : k ≠ l) :
    ¬ Nonempty (preinjectiveRepresentation.{u,v} C k ≅ preinjectiveRepresentation.{u,v} C l) := by
  rintro ⟨e⟩
  have h := tensorIso_target_finrank e
  change Module.finrank (iteratedRightDual N 0).RightRingᵐᵒᵖ (preinjectiveFamily C k 0).obj.Target =
    Module.finrank (iteratedRightDual N 0).RightRingᵐᵒᵖ (preinjectiveFamily C l 0).obj.Target at h
  rw [(preinjectiveFamily C k 0).target_finrank,
    (preinjectiveFamily C l 0).target_finrank] at h
  exact hkl h

end
end QuantumFlags

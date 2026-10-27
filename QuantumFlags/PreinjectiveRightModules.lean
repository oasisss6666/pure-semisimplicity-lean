import QuantumFlags.PreinjectiveEndRings
import QuantumFlags.RepresentationModuleFiniteness

namespace QuantumFlags
noncomputable section
open CategoryTheory
universe u v
variable {N : DivisionBimodule.{u}}

abbrev preinjectiveRightModule (C : RightReflectionChain N) (k : ℕ) :
    ModuleCat.{max u v} (BimoduleTriangularRing N)ᵐᵒᵖ :=
  (bimoduleTensorRepresentationEquivalence N).functor.obj (preinjectiveRepresentation.{u,v} C k)

theorem preinjectiveRightModule_finite (C : RightReflectionChain N) (k : ℕ) :
    Module.Finite (BimoduleTriangularRing N)ᵐᵒᵖ (preinjectiveRightModule.{u,v} C k) := by
  letI : FiniteDimensional N.RightRingᵐᵒᵖ N.Space := C.finite 0
  letI : FiniteDimensional N.LeftRingᵐᵒᵖ (preinjectiveRepresentation.{u,v} C k).Source :=
    (preinjectiveFamily C k 0).sourceFinite
  letI : FiniteDimensional N.RightRingᵐᵒᵖ (preinjectiveRepresentation.{u,v} C k).Target :=
    (preinjectiveFamily C k 0).targetFinite
  exact bimoduleTensorRepresentation_finite N (preinjectiveRepresentation C k)

theorem preinjectiveRightModule_finitelyPresented (C : RightReflectionChain N) (k : ℕ) :
    Module.FinitePresentation (BimoduleTriangularRing N)ᵐᵒᵖ (preinjectiveRightModule.{u,v} C k) := by
  letI : FiniteDimensional N.RightRingᵐᵒᵖ N.Space := C.finite 0
  letI := preinjectiveRightModule_finite.{u,v} C k
  exact bimodule_finite_presentation N (preinjectiveRightModule C k)

theorem preinjectiveRightModule_indecomposable (C : RightReflectionChain N) (k : ℕ) :
    Indecomposable (preinjectiveRightModule.{u,v} C k) :=
  (bimoduleTensorRepresentation_indecomposable_iff N (preinjectiveRepresentation C k)).mpr
    (preinjectiveFamily_indecomposable C k 0)

theorem preinjectiveRightModule_pairwise_nonisomorphic (C : RightReflectionChain N)
    {k l : ℕ} (hkl : k ≠ l) :
    ¬ Nonempty (preinjectiveRightModule.{u,v} C k ≅ preinjectiveRightModule.{u,v} C l) := by
  rintro ⟨e⟩
  exact preinjectiveRepresentation_pairwise_nonisomorphic C hkl
    ⟨(bimoduleTensorRepresentationEquivalence N).fullyFaithfulFunctor.preimageIso e⟩

def preinjectiveRightModuleEndRingEquiv (C : RightReflectionChain N) (k : ℕ) :
    End (preinjectiveRightModule.{u,v} C k) ≃+* (iteratedRightDual N k).LeftRing :=
  by
    have e := preinjectiveFamilyEndRingEquiv.{u,v} C k 0
    rw [Nat.zero_add] at e
    exact (bimoduleTensorRepresentationEndRingEquiv N (preinjectiveRepresentation.{u,v} C k)).symm.trans e

theorem preinjectiveRightModuleEndRingEquiv_exists (C : RightReflectionChain N) (k : ℕ) :
    Nonempty (End (preinjectiveRightModule.{u,v} C k) ≃+* (iteratedRightDual N k).LeftRing) :=
  ⟨preinjectiveRightModuleEndRingEquiv C k⟩

end
end QuantumFlags

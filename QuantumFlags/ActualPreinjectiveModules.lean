import QuantumFlags.ActualPreinjectiveFamily
import QuantumFlags.PreinjectiveRightModules

namespace QuantumFlags
noncomputable section
open CategoryTheory
universe v

abbrev actualPreinjectiveRightModule (k : ℕ) :=
  preinjectiveRightModule.{0,v} actualReflectionChain k

theorem actualPreinjectiveRightModule_finite (k : ℕ) :
    Module.Finite (BimoduleTriangularRing (ambientBimodule (actualFlagSystem.H 1)))ᵐᵒᵖ
      (actualPreinjectiveRightModule.{v} k) :=
  preinjectiveRightModule_finite actualReflectionChain k

theorem actualPreinjectiveRightModule_finitelyPresented (k : ℕ) :
    Module.FinitePresentation (BimoduleTriangularRing (ambientBimodule (actualFlagSystem.H 1)))ᵐᵒᵖ
      (actualPreinjectiveRightModule.{v} k) :=
  preinjectiveRightModule_finitelyPresented actualReflectionChain k

theorem actualPreinjectiveRightModule_indecomposable (k : ℕ) :
    Indecomposable (actualPreinjectiveRightModule.{v} k) :=
  preinjectiveRightModule_indecomposable actualReflectionChain k

theorem actualPreinjectiveRightModule_pairwise_nonisomorphic {k l : ℕ} (h : k ≠ l) :
    ¬ Nonempty (actualPreinjectiveRightModule.{v} k ≅ actualPreinjectiveRightModule.{v} l) :=
  preinjectiveRightModule_pairwise_nonisomorphic actualReflectionChain h

theorem actualPreinjectiveRightModuleEndRingEquiv_exists (k : ℕ) :
    Nonempty (End (actualPreinjectiveRightModule.{v} k) ≃+*
      (iteratedRightDual (ambientBimodule (actualFlagSystem.H 1)) k).LeftRing) :=
  preinjectiveRightModuleEndRingEquiv_exists actualReflectionChain k

end
end QuantumFlags

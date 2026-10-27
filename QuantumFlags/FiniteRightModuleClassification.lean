import QuantumFlags.FiniteIndecomposableClassification
import QuantumFlags.PreinjectiveRightModules

namespace QuantumFlags
noncomputable section
open CategoryTheory
universe u v
variable {N : DivisionBimodule.{u}}

theorem finiteRightModule_indecomposable_classification (C : RightReflectionChain N)
    (hN : Module.finrank N.RightRingᵐᵒᵖ N.Space = 1)
    (M : ModuleCat.{max u v} (BimoduleTriangularRing N)ᵐᵒᵖ)
    [Module.Finite (BimoduleTriangularRing N)ᵐᵒᵖ M] (hM : Indecomposable M) :
    Nonempty (M ≅ (bimoduleTensorRepresentationEquivalence N).functor.obj (tensorSimpleSource.{u,v} N)) ∨
    Nonempty (M ≅ (bimoduleTensorRepresentationEquivalence N).functor.obj (tensorSimpleTarget.{u,v} N)) ∨
    Nonempty (M ≅ (bimoduleTensorRepresentationEquivalence N).functor.obj (tensorCanonicalProjective.{u,v} N)) ∨
    ∃ k : ℕ, 0 < k ∧ Nonempty (M ≅ preinjectiveRightModule.{u,v} C k) := by
  letI : FiniteDimensional N.RightRingᵐᵒᵖ N.Space := C.finite 0
  letI := cornerFixedModule (bimoduleSourceCornerHom N) M
  letI := cornerFixedModule (bimoduleTargetCornerHom N) M
  have hc := (bimodule_finite_iff_corners N M).mp inferInstance
  let E := bimoduleTensorRepresentationEquivalence.{u,v} N
  let Q := E.inverse.obj M
  letI : FiniteDimensional N.LeftRingᵐᵒᵖ Q.Source := hc.1
  letI : FiniteDimensional N.RightRingᵐᵒᵖ Q.Target := hc.2
  have hQ : Indecomposable Q := (equivalence_indecomposable_iff E.symm M).mpr hM
  rcases finiteIndecomposable_classification C hN Q hQ with hS | hT | hP | ⟨k,hk,hI⟩
  · obtain ⟨e⟩ := hS
    exact Or.inl ⟨(E.counitIso.app M).symm ≪≫ E.functor.mapIso e⟩
  · obtain ⟨e⟩ := hT
    exact Or.inr (Or.inl ⟨(E.counitIso.app M).symm ≪≫ E.functor.mapIso e⟩)
  · obtain ⟨e⟩ := hP
    exact Or.inr (Or.inr (Or.inl ⟨(E.counitIso.app M).symm ≪≫ E.functor.mapIso e⟩))
  · obtain ⟨e⟩ := hI
    exact Or.inr (Or.inr (Or.inr ⟨k,hk,⟨(E.counitIso.app M).symm ≪≫ E.functor.mapIso e⟩⟩))

end
end QuantumFlags

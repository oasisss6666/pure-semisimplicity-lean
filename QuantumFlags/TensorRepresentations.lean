import QuantumFlags.BalancedTensor

namespace QuantumFlags
noncomputable section
universe u

structure TensorRepresentation (N : DivisionBimodule.{u}) where
  Source : Type*
  Target : Type*
  [sourceGroup : AddCommGroup Source]
  [targetGroup : AddCommGroup Target]
  [sourceModule : Module N.LeftRingᵐᵒᵖ Source]
  [targetModule : Module N.RightRingᵐᵒᵖ Target]
  arrow : BalancedTensor N Source →ₗ[N.RightRingᵐᵒᵖ] Target

attribute [instance] TensorRepresentation.sourceGroup TensorRepresentation.targetGroup
  TensorRepresentation.sourceModule TensorRepresentation.targetModule

structure TensorRepresentationMorphism {N : DivisionBimodule.{u}}
    (M P : TensorRepresentation N) where
  source : M.Source →ₗ[N.LeftRingᵐᵒᵖ] P.Source
  target : M.Target →ₗ[N.RightRingᵐᵒᵖ] P.Target
  commutes : ∀ z, P.arrow (balancedTensorMap N M.Source source z) = target (M.arrow z)

abbrev tensorRepresentationToHom {N : DivisionBimodule.{u}} (M : TensorRepresentation N) :
    HomRepresentation N where
  Source := M.Source
  Target := M.Target
  arrow := balancedTensorCurry N M.Source M.arrow

abbrev homRepresentationToTensor {N : DivisionBimodule.{u}} (M : HomRepresentation N) :
    TensorRepresentation N where
  Source := M.Source
  Target := M.Target
  arrow := balancedTensorLift N M.Source M.arrow

theorem homRepresentationToTensor_pure {N : DivisionBimodule.{u}} (M : HomRepresentation N)
    (x : M.Source) (n : N.Space) :
    (homRepresentationToTensor M).arrow (balancedPure N M.Source x n) = M.arrow x n :=
  balancedTensorLift_pure N M.Source M.arrow x n

def tensorMorphismToHom {N : DivisionBimodule.{u}} {M P : TensorRepresentation N}
    (f : TensorRepresentationMorphism M P) :
    HomRepresentationMorphism (tensorRepresentationToHom M) (tensorRepresentationToHom P) where
  source := f.source
  target := f.target
  commutes x := by
    apply LinearMap.ext
    intro n
    have h := f.commutes (balancedPure N M.Source x n)
    rw [balancedTensorMap_pure] at h
    exact h

def homMorphismToTensor {N : DivisionBimodule.{u}} {M P : HomRepresentation N}
    (f : HomRepresentationMorphism M P) :
    TensorRepresentationMorphism (homRepresentationToTensor M) (homRepresentationToTensor P) where
  source := f.source
  target := f.target
  commutes z := by
    have h : (homRepresentationToTensor P).arrow.comp (balancedTensorMap N M.Source f.source) =
        f.target.comp (homRepresentationToTensor M).arrow := by
      apply balancedTensor_ext N M.Source
      intro x n
      simp only [LinearMap.comp_apply, balancedTensorMap_pure, balancedTensorLift_pure]
      exact LinearMap.congr_fun (f.commutes x) n
    exact LinearMap.congr_fun h z

theorem tensorHom_arrow_roundtrip {N : DivisionBimodule.{u}} (M : TensorRepresentation N) :
    (homRepresentationToTensor (tensorRepresentationToHom M)).arrow = M.arrow :=
  (balancedTensorHomEquiv N M.Source).symm_apply_apply M.arrow

theorem homTensor_arrow_roundtrip {N : DivisionBimodule.{u}} (M : HomRepresentation N) :
    letI := rightHomModule N M.Target
    (tensorRepresentationToHom (homRepresentationToTensor M)).arrow = M.arrow :=
  (balancedTensorHomEquiv N M.Source).apply_symm_apply M.arrow

end
end QuantumFlags

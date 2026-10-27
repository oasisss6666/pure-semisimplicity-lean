import QuantumFlags.TensorRepresentationMaps

namespace QuantumFlags
noncomputable section
universe u
variable {N : DivisionBimodule.{u}} {M P : TensorRepresentation N}

def homMorphismFromTensorArrows
    (f : HomRepresentationMorphism (tensorRepresentationToHom M) (tensorRepresentationToHom P)) :
    TensorRepresentationMorphism M P where
  source := f.source
  target := f.target
  commutes z := by
    have h : P.arrow.comp (balancedTensorMap N M.Source f.source) = f.target.comp M.arrow := by
      apply balancedTensor_ext N M.Source
      intro x n
      simp only [LinearMap.comp_apply, balancedTensorMap_pure]
      exact LinearMap.congr_fun (f.commutes x) n
    exact LinearMap.congr_fun h z

def tensorHomMorphismEquiv : TensorRepresentationMorphism M P ≃
    HomRepresentationMorphism (tensorRepresentationToHom M) (tensorRepresentationToHom P) where
  toFun := tensorMorphismToHom
  invFun := homMorphismFromTensorArrows
  left_inv f := by apply TensorRepresentationMorphism.ext <;> rfl
  right_inv f := by apply HomRepresentationMorphism.ext <;> rfl

theorem tensorMorphismToHom_identity (L : TensorRepresentation N) :
    tensorMorphismToHom (TensorRepresentationMorphism.identity L) =
      HomRepresentationMorphism.identity (tensorRepresentationToHom L) := by
  apply HomRepresentationMorphism.ext <;> rfl

theorem tensorMorphismToHom_comp {Q : TensorRepresentation N}
    (g : TensorRepresentationMorphism P Q) (f : TensorRepresentationMorphism M P) :
    tensorMorphismToHom (TensorRepresentationMorphism.compose g f) =
      HomRepresentationMorphism.compose (tensorMorphismToHom g) (tensorMorphismToHom f) := by
  apply HomRepresentationMorphism.ext <;> rfl

end
end QuantumFlags

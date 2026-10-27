import QuantumFlags.TensorRepresentations

namespace QuantumFlags
noncomputable section
universe u
namespace TensorRepresentationMorphism
variable {N : DivisionBimodule.{u}} {M P Q R : TensorRepresentation N}

def identity (M : TensorRepresentation N) : TensorRepresentationMorphism M M where
  source := LinearMap.id
  target := LinearMap.id
  commutes z := by rw [balancedTensorMap_identity]; rfl

def compose (g : TensorRepresentationMorphism P Q) (f : TensorRepresentationMorphism M P) :
    TensorRepresentationMorphism M Q where
  source := g.source.comp f.source
  target := g.target.comp f.target
  commutes z := by
    rw [balancedTensorMap_comp, LinearMap.comp_apply, g.commutes, f.commutes]
    rfl

theorem ext {f g : TensorRepresentationMorphism M P}
    (hs : f.source = g.source) (ht : f.target = g.target) : f = g := by
  cases f
  cases g
  cases hs
  cases ht
  rfl

theorem compose_identity (f : TensorRepresentationMorphism M P) : compose f (identity M) = f := by
  apply ext <;> rfl

theorem identity_compose (f : TensorRepresentationMorphism M P) : compose (identity P) f = f := by
  apply ext <;> rfl

theorem compose_assoc (h : TensorRepresentationMorphism Q R) (g : TensorRepresentationMorphism P Q)
    (f : TensorRepresentationMorphism M P) : compose (compose h g) f = compose h (compose g f) := by
  apply ext <;> rfl

end TensorRepresentationMorphism
end
end QuantumFlags

import QuantumFlags.TensorHomMorphismEquivalence
import Mathlib.Algebra.Group.TransferInstance

namespace QuantumFlags
noncomputable section
universe u
namespace HomRepresentationMorphism
variable {N : DivisionBimodule.{u}} (M P : HomRepresentation N)

def compatiblePairs : AddSubgroup
    ((M.Source →ₗ[N.LeftRingᵐᵒᵖ] P.Source) × (M.Target →ₗ[N.RightRingᵐᵒᵖ] P.Target)) where
  carrier := {f | ∀ x n, P.arrow (f.1 x) n = f.2 (M.arrow x n)}
  zero_mem' := by
    intro x n
    change P.arrow 0 n = 0
    rw [map_zero]
    rfl
  add_mem' := by
    intro f g hf hg x n
    change P.arrow (f.1 x+g.1 x) n = f.2 (M.arrow x n)+g.2 (M.arrow x n)
    rw [map_add]
    exact congrArg₂ (· + ·) (hf x n) (hg x n)
  neg_mem' := by
    intro f hf x n
    change P.arrow (-f.1 x) n = -f.2 (M.arrow x n)
    rw [map_neg]
    exact congrArg Neg.neg (hf x n)

def pairEquiv : HomRepresentationMorphism M P ≃ compatiblePairs M P where
  toFun f := ⟨(f.source,f.target), fun x n => LinearMap.congr_fun (f.commutes x) n⟩
  invFun f := {
    source := f.val.1
    target := f.val.2
    commutes x := by apply LinearMap.ext; intro n; exact f.property x n }
  left_inv f := by apply ext <;> rfl
  right_inv f := by apply Subtype.ext; rfl

instance addCommGroup : AddCommGroup (HomRepresentationMorphism M P) :=
  (pairEquiv M P).addCommGroup

variable {M P}

theorem add_source (f g : HomRepresentationMorphism M P) : (f+g).source = f.source+g.source := rfl

theorem add_target (f g : HomRepresentationMorphism M P) : (f+g).target = f.target+g.target := rfl

theorem zero_source : (0 : HomRepresentationMorphism M P).source = 0 := rfl

theorem zero_target : (0 : HomRepresentationMorphism M P).target = 0 := rfl

theorem neg_source (f : HomRepresentationMorphism M P) : (-f).source = -f.source := rfl

theorem neg_target (f : HomRepresentationMorphism M P) : (-f).target = -f.target := rfl

end HomRepresentationMorphism
namespace TensorRepresentationMorphism
variable {N : DivisionBimodule.{u}} (M P : TensorRepresentation N)

instance addCommGroup : AddCommGroup (TensorRepresentationMorphism M P) :=
  (tensorHomMorphismEquiv (M := M) (P := P)).addCommGroup

variable {M P}

theorem add_source (f g : TensorRepresentationMorphism M P) : (f+g).source = f.source+g.source := rfl

theorem add_target (f g : TensorRepresentationMorphism M P) : (f+g).target = f.target+g.target := rfl

theorem zero_source : (0 : TensorRepresentationMorphism M P).source = 0 := rfl

theorem zero_target : (0 : TensorRepresentationMorphism M P).target = 0 := rfl

theorem neg_source (f : TensorRepresentationMorphism M P) : (-f).source = -f.source := rfl

theorem neg_target (f : TensorRepresentationMorphism M P) : (-f).target = -f.target := rfl

end TensorRepresentationMorphism
end
end QuantumFlags

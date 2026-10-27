import QuantumFlags.PositiveDefectClassification
import QuantumFlags.ZeroDefectIndecomposable
import QuantumFlags.IndecomposableDimensionBounds

/-!
# The merged finite classification at layer 0

Manuscript `prop:class` (source lines 212-220): a finite-dimensional indecomposable
representation of `N_0` is the simple source, the simple target, the canonical projective `P`,
or one of the modules `I_k` with `k ≥ 1`.  The zero-defect branch `a = b` is
`nonsimple_zeroDefect_classification`, and the positive-defect branch `a > b` is
`positiveDefect_classification`; the member `I_0` of the preinjective family is the simple
source and is returned to that case.
-/

namespace QuantumFlags
noncomputable section
open CategoryTheory
universe u v
variable {N : DivisionBimodule.{u}}

/-- An object isomorphic to the layer-0 member of index `b` of the preinjective family is the
simple source when `b = 0`, and one of the manuscript's `I_k` with `k ≥ 1` otherwise. -/
theorem preinjectiveFamily_layer_zero_cases (C : RightReflectionChain N)
    (M : TensorRepresentation.{u,max u v,max u v} N) (b : ℕ)
    (e : M ≅ (preinjectiveFamily.{u,v} C b 0).obj) :
    Nonempty (M ≅ tensorSimpleSource.{u,v} N) ∨
      ∃ k : ℕ, 0 < k ∧ Nonempty (M ≅ preinjectiveRepresentation.{u,v} C k) := by
  cases b with
  | zero => exact Or.inl ⟨e⟩
  | succ k => exact Or.inr ⟨k + 1, Nat.succ_pos k, ⟨e⟩⟩

/-- Manuscript `prop:class`, list of finite indecomposables: every finite-dimensional
indecomposable tensor representation of `N` is isomorphic to the simple source, the simple
target, the canonical projective, or some `I_k` with `k ≥ 1`. -/
theorem finiteIndecomposable_classification (C : RightReflectionChain N)
    (hN : Module.finrank N.RightRingᵐᵒᵖ N.Space = 1)
    (M : TensorRepresentation.{u,max u v,max u v} N)
    [hMS : FiniteDimensional N.LeftRingᵐᵒᵖ M.Source]
    [hMT : FiniteDimensional N.RightRingᵐᵒᵖ M.Target] (hM : Indecomposable M) :
    Nonempty (M ≅ tensorSimpleSource.{u,v} N) ∨
    Nonempty (M ≅ tensorSimpleTarget.{u,v} N) ∨
    Nonempty (M ≅ tensorCanonicalProjective.{u,v} N) ∨
    ∃ k : ℕ, 0 < k ∧ Nonempty (M ≅ preinjectiveRepresentation.{u,v} C k) := by
  by_cases hS : Nonempty (M ≅ tensorSimpleSource.{u,v} N)
  · exact Or.inl hS
  by_cases hT : Nonempty (M ≅ tensorSimpleTarget.{u,v} N)
  · exact Or.inr (Or.inl hT)
  letI : FiniteDimensional N.RightRingᵐᵒᵖ N.Space := C.finite 0
  letI := dualRightModule N
  letI : FiniteDimensional N.LeftRingᵐᵒᵖ (RightDualSpace N) := C.finite 1
  have hD : Module.finrank N.LeftRingᵐᵒᵖ (RightDualSpace N) = 2 := C.double 0
  have hbounds := one_two_indecomposable_dimension_bounds N M hN hD hM hS hT
  by_cases heq : Module.finrank N.LeftRingᵐᵒᵖ M.Source =
      Module.finrank N.RightRingᵐᵒᵖ M.Target
  · exact Or.inr (Or.inr (Or.inl (nonsimple_zeroDefect_classification N M hN hM hT heq)))
  · have hpos : Module.finrank N.RightRingᵐᵒᵖ M.Target <
        Module.finrank N.LeftRingᵐᵒᵖ M.Source := by omega
    -- `iteratedRightDual N 0` is `N` by definition; the layer-0 instances are passed explicitly.
    obtain ⟨e⟩ := @positiveDefect_classification.{u,v} N C 0 M hMS hMT hM hpos
    rcases preinjectiveFamily_layer_zero_cases C M _ e with h | h
    · exact absurd h hS
    · exact Or.inr (Or.inr (Or.inr h))

end
end QuantumFlags

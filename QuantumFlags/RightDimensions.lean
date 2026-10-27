import QuantumFlags.FlagSystem
import Mathlib.Algebra.Module.Opposite
import Mathlib.Algebra.Module.RingHom
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free

namespace QuantumFlags

noncomputable section

variable {D : Type*} [DivisionRing D]

/-- Right vector spaces over a subdivision ring are left vector spaces over
its opposite division ring. -/
instance rightSubfieldModule (H : Subfield D) : Module Hᵐᵒᵖ D :=
  Module.compHom D H.subtype.op

theorem rightSubfield_smul (H : Subfield D) (c : Hᵐᵒᵖ) (a : D) :
    c • a = a*(c.unop : D) := rfl

def rightWideLinear (H : Subfield D) {I : Type*} [Fintype I] (w : I → D) :
    (I → Hᵐᵒᵖ) →ₗ[Hᵐᵒᵖ] D where
  toFun c := ∑ i, w i*(c i).unop
  map_add' c d := by
    simp only [Pi.add_apply, MulOpposite.unop_add, Subfield.coe_add, mul_add, Finset.sum_add_distrib]
  map_smul' a c := by
    change (∑ i, w i*((a*(c i)).unop : D)) = (∑ i, w i*((c i).unop : D))*(a.unop : D)
    simp only [MulOpposite.unop_mul, Subfield.coe_mul, Finset.sum_mul, mul_assoc]

theorem rightWideLinear_bijective (H : Subfield D) {I : Type*} [Fintype I] (w : I → D)
    (h : Function.Bijective (wideEval H.subtype w)) :
    Function.Bijective (rightWideLinear H w) := by
  constructor
  · intro c d hcd
    have he : (fun i => (c i).unop) = (fun i => (d i).unop) := h.injective hcd
    funext i
    exact MulOpposite.unop_injective (congrFun he i)
  · intro a
    obtain ⟨c, hc⟩ := h.surjective a
    exact ⟨fun i => MulOpposite.op (c i), hc⟩

def rightBasisEquiv (S : FlagSystem D) (r : ℕ) :
    (Fin (r+1) → (S.H r)ᵐᵒᵖ) ≃ₗ[(S.H r)ᵐᵒᵖ] D :=
  LinearEquiv.ofBijective (rightWideLinear (S.H r) (fun i : Fin (r+1) => S.t^i.val))
    (rightWideLinear_bijective _ _ (S.right_basis r))

instance flag_right_finiteDimensional (S : FlagSystem D) (r : ℕ) :
    FiniteDimensional (S.H r)ᵐᵒᵖ D :=
  FiniteDimensional.of_injective (rightBasisEquiv S r).symm.toLinearMap
    (rightBasisEquiv S r).symm.injective

theorem flag_right_finrank (S : FlagSystem D) (r : ℕ) :
    Module.finrank (S.H r)ᵐᵒᵖ D = r+1 := by
  rw [← (rightBasisEquiv S r).finrank_eq, Module.finrank_pi, Fintype.card_fin]

end

end QuantumFlags

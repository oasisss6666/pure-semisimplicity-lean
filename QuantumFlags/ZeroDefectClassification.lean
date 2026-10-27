import QuantumFlags.CanonicalProjectiveArrow
import QuantumFlags.InvertibleTensorArrows
import QuantumFlags.BalancedTensorDimensions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace QuantumFlags
noncomputable section
open CategoryTheory
universe u v
variable (N : DivisionBimodule.{u})
variable (M : TensorRepresentation.{u,max u v,max u v} N)

theorem indecomposable_invertibleArrow_isCanonicalProjective
    (hM : Indecomposable M) (hbij : Function.Bijective M.arrow)
    (hx : ∃ x : M.Source, x ≠ 0) :
    Nonempty (M ≅ tensorCanonicalProjective.{u,v} N) := by
  obtain ⟨x,hx⟩ := hx
  obtain ⟨p,hp⟩ := (scalarLine N.LeftRingᵐᵒᵖ x).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (scalarLine_injective N.LeftRingᵐᵒᵖ hx))
  let e : ULift.{v} N.LeftRingᵐᵒᵖ ≃ₗ[N.LeftRingᵐᵒᵖ] N.LeftRingᵐᵒᵖ := ULift.moduleEquiv
  let s : (tensorCanonicalProjective.{u,v} N).Source →ₗ[N.LeftRingᵐᵒᵖ] M.Source :=
    (scalarLine N.LeftRingᵐᵒᵖ x).comp e.toLinearMap
  let r : M.Source →ₗ[N.LeftRingᵐᵒᵖ] (tensorCanonicalProjective.{u,v} N).Source :=
    e.symm.toLinearMap.comp p
  have hrs : r.comp s = LinearMap.id := by
    apply LinearMap.ext; intro a
    change e.symm (p (scalarLine N.LeftRingᵐᵒᵖ x (e a))) = a
    have h := LinearMap.congr_fun hp (e a)
    change p (scalarLine N.LeftRingᵐᵒᵖ x (e a)) = e a at h
    rw [h, LinearEquiv.symm_apply_apply]
  let i : tensorCanonicalProjective.{u,v} N ⟶ M :=
    invertibleTensorArrowMorphism (canonicalProjective_tensorArrow_bijective N) s
  let q : M ⟶ tensorCanonicalProjective.{u,v} N :=
    invertibleTensorArrowMorphism hbij r
  apply indecomposable_tensor_retract_isomorphism hM
    (tensorCanonicalProjective_indecomposable N).1 i q
  apply invertibleTensorArrowMorphism_ext (canonicalProjective_tensorArrow_bijective N).surjective
  exact hrs

variable [FiniteDimensional N.RightRingᵐᵒᵖ N.Space]
  [FiniteDimensional N.LeftRingᵐᵒᵖ M.Source]
  [FiniteDimensional N.RightRingᵐᵒᵖ M.Target]

theorem zeroDefect_tensorArrow_bijective
    (hN : Module.finrank N.RightRingᵐᵒᵖ N.Space = 1)
    (heq : Module.finrank N.LeftRingᵐᵒᵖ M.Source = Module.finrank N.RightRingᵐᵒᵖ M.Target)
    (hSurj : Function.Surjective M.arrow) : Function.Bijective M.arrow := by
  have hd : Module.finrank N.RightRingᵐᵒᵖ (BalancedTensor N M.Source) =
      Module.finrank N.RightRingᵐᵒᵖ M.Target := by
    rw [balancedTensor_finrank, hN, mul_one, heq]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr hSurj, hSurj⟩

theorem zeroDefect_indecomposable_isCanonicalProjective
    (hN : Module.finrank N.RightRingᵐᵒᵖ N.Space = 1)
    (heq : Module.finrank N.LeftRingᵐᵒᵖ M.Source = Module.finrank N.RightRingᵐᵒᵖ M.Target)
    (hpos : 0 < Module.finrank N.LeftRingᵐᵒᵖ M.Source)
    (hM : Indecomposable M) (hSurj : Function.Surjective M.arrow) :
    Nonempty (M ≅ tensorCanonicalProjective.{u,v} N) := by
  exact indecomposable_invertibleArrow_isCanonicalProjective N M hM
    (zeroDefect_tensorArrow_bijective N M hN heq hSurj)
    (Module.finrank_pos_iff_exists_ne_zero.mp hpos)

end
end QuantumFlags

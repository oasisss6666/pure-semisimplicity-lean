import QuantumFlags.TensorSimpleSummands
import QuantumFlags.RepresentationMorphismAddition

namespace QuantumFlags
noncomputable section
universe u v
variable (N : DivisionBimodule.{u})
local instance simpleVanishingHomModule (Y : Type*) [AddCommGroup Y]
    [Module N.RightRingᵐᵒᵖ Y] : Module N.LeftRingᵐᵒᵖ (BimoduleRightHom N Y) := rightHomModule N Y

theorem homFromSimpleSource_eq_zero (M : HomRepresentation.{u,max u v,max u v} N)
    (hM : Function.Injective M.arrow)
    (f : HomRepresentationMorphism (simpleSource.{u,v} N) M) : f = 0 := by
  apply HomRepresentationMorphism.ext
  · apply LinearMap.ext
    intro x
    change f.source x = 0
    apply hM
    rw [map_zero]
    have h := f.commutes x
    change M.arrow (f.source x) = f.target.comp 0 at h
    simpa only [LinearMap.comp_zero] using h
  · apply LinearMap.ext
    intro y
    have hy : y = 0 := Subsingleton.elim _ _
    rw [hy, map_zero]
    rfl

theorem tensorHomFromSimpleSource_eq_zero (M : TensorRepresentation.{u,max u v,max u v} N)
    (hM : Function.Injective (tensorRepresentationToHom M).arrow)
    (f : TensorRepresentationMorphism (tensorSimpleSource.{u,v} N) M) : f = 0 := by
  apply tensorHomMorphismEquiv.injective
  exact homFromSimpleSource_eq_zero N (tensorRepresentationToHom M) hM (tensorMorphismToHom f)

theorem tensorHomToSimpleTarget_eq_zero (M : TensorRepresentation.{u,max u v,max u v} N)
    (hM : Function.Surjective M.arrow)
    (f : TensorRepresentationMorphism M (tensorSimpleTarget.{u,v} N)) : f = 0 := by
  apply TensorRepresentationMorphism.ext
  · apply LinearMap.ext
    intro x
    exact Subsingleton.elim _ _
  · apply LinearMap.ext
    intro y
    obtain ⟨z, rfl⟩ := hM y
    have h := f.commutes z
    change 0 = f.target (M.arrow z) at h
    exact h.symm

end
end QuantumFlags

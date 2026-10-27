import QuantumFlags.ReflectionEndomorphismRings

namespace QuantumFlags
noncomputable section
open CategoryTheory
universe u v
variable (N : DivisionBimodule.{u}) [FiniteDimensional N.RightRingᵐᵒᵖ N.Space]
variable (M : InjectiveHomObjects.{u,v} N)

theorem reflection_identity_zero_iff :
    (1 : End M) = 0 ↔ (1 : End ((reflectionFunctor N).obj M)) = 0 := by
  let e := reflectionEndRingEquiv N M
  constructor
  · intro h
    have he := congrArg e h
    simpa only [map_one,map_zero] using he
  · intro h
    apply e.injective
    simpa only [map_one,map_zero] using h

theorem reflection_trivial_idempotents_iff :
    (∀ f : End M, f*f = f → f = 0 ∨ f = 1) ↔
      (∀ g : End ((reflectionFunctor N).obj M), g*g = g → g = 0 ∨ g = 1) := by
  let e := reflectionEndRingEquiv N M
  constructor
  · intro h g hg
    obtain ⟨f,rfl⟩ := e.surjective g
    have hf : f*f = f := e.injective (by simpa only [map_mul] using hg)
    rcases h f hf with h0 | h1
    · left; simpa only [h0,map_zero]
    · right; simpa only [h1,map_one]
  · intro h f hf
    have hg : e f * e f = e f := by rw [← map_mul,hf]
    rcases h (e f) hg with h0 | h1
    · left; apply e.injective; simpa only [map_zero] using h0
    · right; apply e.injective; simpa only [map_one] using h1

end
end QuantumFlags

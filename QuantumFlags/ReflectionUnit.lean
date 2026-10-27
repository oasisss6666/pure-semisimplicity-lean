import QuantumFlags.ReflectionObjects

namespace QuantumFlags
noncomputable section
universe u v
variable (N : DivisionBimodule.{u}) [FiniteDimensional N.RightRingᵐᵒᵖ N.Space]
local instance reflectionUnitDualModule : Module N.LeftRingᵐᵒᵖ (RightDualSpace N) := dualRightModule N
local instance reflectionUnitHomModule (Y : Type*) [AddCommGroup Y] [Module N.RightRingᵐᵒᵖ Y] :
    Module N.LeftRingᵐᵒᵖ (BimoduleRightHom N Y) := rightHomModule N Y

variable (M : HomRepresentation.{u, max u v, max u v} N)

def reflectionUnitSourceMap : M.Source →ₗ[N.LeftRingᵐᵒᵖ]
    (reflectionBackward N (reflectionForward N M)).Source where
  toFun x := ⟨(dualTensorHomEquiv N M.Target).symm (M.arrow x), by
    change M.arrow.range.mkQ (dualTensorHomEquiv N M.Target
      ((dualTensorHomEquiv N M.Target).symm (M.arrow x))) = 0
    rw [LinearEquiv.apply_symm_apply]
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x,rfl⟩⟩
  map_add' x y := by
    apply Subtype.ext
    change (dualTensorHomEquiv N M.Target).symm (M.arrow (x+y)) =
      (dualTensorHomEquiv N M.Target).symm (M.arrow x)+(dualTensorHomEquiv N M.Target).symm (M.arrow y)
    rw [map_add,map_add]
  map_smul' a x := by
    apply Subtype.ext
    change (dualTensorHomEquiv N M.Target).symm (M.arrow (a • x)) =
      a • (dualTensorHomEquiv N M.Target).symm (M.arrow x)
    rw [map_smul,map_smul]

theorem reflectionUnitSourceMap_surjective : Function.Surjective (reflectionUnitSourceMap N M) := by
  intro z
  have hz : M.arrow.range.mkQ (dualTensorHomEquiv N M.Target z.val) = 0 := z.property
  obtain ⟨x,hx⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz
  refine ⟨x, Subtype.ext ?_⟩
  change (dualTensorHomEquiv N M.Target).symm (M.arrow x) = z.val
  rw [hx,LinearEquiv.symm_apply_apply]

theorem reflectionUnitSourceMap_injective (hM : Function.Injective M.arrow) :
    Function.Injective (reflectionUnitSourceMap N M) := by
  intro x y h
  apply hM
  have he := congrArg Subtype.val h
  change (dualTensorHomEquiv N M.Target).symm (M.arrow x) =
    (dualTensorHomEquiv N M.Target).symm (M.arrow y) at he
  exact (dualTensorHomEquiv N M.Target).symm.injective he

def reflectionUnitSourceEquiv (hM : Function.Injective M.arrow) :
    M.Source ≃ₗ[N.LeftRingᵐᵒᵖ] (reflectionBackward N (reflectionForward N M)).Source :=
  LinearEquiv.ofBijective (reflectionUnitSourceMap N M)
    ⟨reflectionUnitSourceMap_injective N M hM,reflectionUnitSourceMap_surjective N M⟩

def reflectionUnit : HomRepresentationMorphism M (reflectionBackward N (reflectionForward N M)) where
  source := reflectionUnitSourceMap N M
  target := LinearMap.id
  commutes x := by
    change dualTensorHomEquiv N M.Target ((dualTensorHomEquiv N M.Target).symm (M.arrow x)) = M.arrow x
    exact LinearEquiv.apply_symm_apply _ _

def reflectionUnitInverse (hM : Function.Injective M.arrow) :
    HomRepresentationMorphism (reflectionBackward N (reflectionForward N M)) M where
  source := (reflectionUnitSourceEquiv N M hM).symm.toLinearMap
  target := LinearMap.id
  commutes z := by
    have h := (reflectionUnit N M).commutes ((reflectionUnitSourceEquiv N M hM).symm z)
    change (reflectionBackward N (reflectionForward N M)).arrow
      (reflectionUnitSourceEquiv N M hM ((reflectionUnitSourceEquiv N M hM).symm z)) =
      M.arrow ((reflectionUnitSourceEquiv N M hM).symm z) at h
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm

theorem reflectionUnit_left_inverse (hM : Function.Injective M.arrow) :
    HomRepresentationMorphism.compose (reflectionUnitInverse N M hM) (reflectionUnit N M) =
      HomRepresentationMorphism.identity M := by
  apply HomRepresentationMorphism.ext
  · apply LinearMap.ext
    intro x
    exact (reflectionUnitSourceEquiv N M hM).symm_apply_apply x
  · rfl

theorem reflectionUnit_right_inverse (hM : Function.Injective M.arrow) :
    HomRepresentationMorphism.compose (reflectionUnit N M) (reflectionUnitInverse N M hM) =
      HomRepresentationMorphism.identity (reflectionBackward N (reflectionForward N M)) := by
  apply HomRepresentationMorphism.ext
  · apply LinearMap.ext
    intro z
    exact (reflectionUnitSourceEquiv N M hM).apply_symm_apply z
  · rfl

theorem reflectionUnit_natural {P : HomRepresentation.{u, max u v, max u v} N}
    (f : HomRepresentationMorphism M P) :
    HomRepresentationMorphism.compose (reflectionBackwardMap N (reflectionForwardMap N f))
      (reflectionUnit N M) =
      HomRepresentationMorphism.compose (reflectionUnit N P) f := by
  apply HomRepresentationMorphism.ext
  · apply LinearMap.ext
    intro x
    apply Subtype.ext
    change balancedTensorMap (rightDual N) M.Target f.target
      ((dualTensorHomEquiv N M.Target).symm (M.arrow x)) =
      (dualTensorHomEquiv N P.Target).symm (P.arrow (f.source x))
    apply (dualTensorHomEquiv N P.Target).injective
    have hn := LinearMap.congr_fun (dualTensorHomEquiv_natural N M.Target f.target)
      ((dualTensorHomEquiv N M.Target).symm (M.arrow x))
    change rightHomMap N f.target (dualTensorHomEquiv N M.Target
      ((dualTensorHomEquiv N M.Target).symm (M.arrow x))) =
      dualTensorHomEquiv N P.Target (balancedTensorMap (rightDual N) M.Target f.target
        ((dualTensorHomEquiv N M.Target).symm (M.arrow x))) at hn
    rw [LinearEquiv.apply_symm_apply] at hn
    rw [← hn,LinearEquiv.apply_symm_apply]
    exact (f.commutes x).symm
  · rfl

end
end QuantumFlags

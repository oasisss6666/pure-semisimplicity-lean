import QuantumFlags.HomRepresentationCategory
import QuantumFlags.SplitKernelProjection

namespace QuantumFlags
noncomputable section
universe u
variable {N : DivisionBimodule.{u}}
local instance kernelRepresentationHomModule (Y : Type*) [AddCommGroup Y]
    [Module N.RightRingᵐᵒᵖ Y] : Module N.LeftRingᵐᵒᵖ (BimoduleRightHom N Y) := rightHomModule N Y

abbrev homRepresentationKernel {M S : HomRepresentation N}
    (p : HomRepresentationMorphism M S) : HomRepresentation N where
  Source := p.source.ker
  Target := p.target.ker
  arrow := {
    toFun x := {
      toFun n := ⟨M.arrow x n, by
        have h := LinearMap.congr_fun (p.commutes (x : M.Source)) n
        change S.arrow (p.source x) n = p.target (M.arrow x n) at h
        rw [x.property, map_zero] at h
        exact h.symm⟩
      map_add' n m := by
        apply Subtype.ext
        exact (M.arrow x).map_add n m
      map_smul' b n := by
        apply Subtype.ext
        exact (M.arrow x).map_smul b n }
    map_add' x y := by
      apply LinearMap.ext
      intro n
      apply Subtype.ext
      exact LinearMap.congr_fun (M.arrow.map_add (x : M.Source) (y : M.Source)) n
    map_smul' a x := by
      apply LinearMap.ext
      intro n
      apply Subtype.ext
      exact LinearMap.congr_fun (M.arrow.map_smul a (x : M.Source)) n }

def homRepresentationKernelInclusion {M S : HomRepresentation N}
    (p : HomRepresentationMorphism M S) :
    HomRepresentationMorphism (homRepresentationKernel p) M where
  source := p.source.ker.subtype
  target := p.target.ker.subtype
  commutes x := by apply LinearMap.ext; intro n; rfl

def homRepresentationKernelProjection {M S : HomRepresentation N}
    (i : HomRepresentationMorphism S M) (p : HomRepresentationMorphism M S)
    (hpi : HomRepresentationMorphism.compose p i = HomRepresentationMorphism.identity S) :
    HomRepresentationMorphism M (homRepresentationKernel p) where
  source := splitKernelProjection i.source p.source (congrArg HomRepresentationMorphism.source hpi)
  target := splitKernelProjection i.target p.target (congrArg HomRepresentationMorphism.target hpi)
  commutes x := by
    apply LinearMap.ext
    intro n
    apply Subtype.ext
    change M.arrow (x-i.source (p.source x)) n =
      M.arrow x n - i.target (p.target (M.arrow x n))
    rw [map_sub, LinearMap.sub_apply, i.commutes, p.commutes]
    rfl

end
end QuantumFlags

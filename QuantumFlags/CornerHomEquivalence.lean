import QuantumFlags.TriangularRepresentationMaps

namespace QuantumFlags

noncomputable section

variable {D : Type*} [DivisionRing D]

theorem cornerDecomposition_source (H : Subfield D) (M : Type*) [AddCommGroup M]
    [Module (TriangularRing H)ᵐᵒᵖ M] (x : SourceCorner H M) :
    cornerDecomposition H M (x : M) = (x,0) := by
  have h := (cornerDecomposition H M).apply_symm_apply (x,0)
  change cornerDecomposition H M ((x : M)+(0 : M)) = (x,0) at h
  simpa only [add_zero] using h

theorem cornerDecomposition_target (H : Subfield D) (M : Type*) [AddCommGroup M]
    [Module (TriangularRing H)ᵐᵒᵖ M] (x : TargetCorner H M) :
    cornerDecomposition H M (x : M) = (0,x) := by
  have h := (cornerDecomposition H M).apply_symm_apply (0,x)
  change cornerDecomposition H M ((0 : M)+(x : M)) = (0,x) at h
  simpa only [zero_add] using h

theorem cornerRepresentationMorphism_arrow (H : Subfield D) {M : Type*} {P : Type*}
    [AddCommGroup M] [Module (TriangularRing H)ᵐᵒᵖ M]
    [AddCommGroup P] [Module (TriangularRing H)ᵐᵒᵖ P]
    (f : HomRepresentationMorphism (cornerHomRepresentation H M) (cornerHomRepresentation H P))
    (x : SourceCorner H M) : cornerArrow H P (f.source x) = f.target (cornerArrow H M x) := by
  have h := congrArg (fun φ => φ 1) (f.commutes x)
  change MulOpposite.op (1 : D) • cornerArrow H P (f.source x) =
    f.target (MulOpposite.op (1 : D) • cornerArrow H M x) at h
  simpa using h

def moduleMapFromCornerHom (H : Subfield D) {M : Type*} {P : Type*}
    [AddCommGroup M] [Module (TriangularRing H)ᵐᵒᵖ M]
    [AddCommGroup P] [Module (TriangularRing H)ᵐᵒᵖ P]
    (f : HomRepresentationMorphism (cornerHomRepresentation H M) (cornerHomRepresentation H P)) :
    M →ₗ[(TriangularRing H)ᵐᵒᵖ] P := by
  letI := triangularModuleFromArrow H (SourceCorner H M) (TargetCorner H M) (cornerArrow H M)
  letI := triangularModuleFromArrow H (SourceCorner H P) (TargetCorner H P) (cornerArrow H P)
  exact (cornerModuleEquiv H P).symm.toLinearMap.comp
    ((triangularMapFromArrows H (cornerArrow H M) (cornerArrow H P) f.source f.target
      (cornerRepresentationMorphism_arrow H f)).comp (cornerModuleEquiv H M).toLinearMap)

theorem moduleMapFromCornerHom_apply (H : Subfield D) {M : Type*} {P : Type*}
    [AddCommGroup M] [Module (TriangularRing H)ᵐᵒᵖ M]
    [AddCommGroup P] [Module (TriangularRing H)ᵐᵒᵖ P]
    (f : HomRepresentationMorphism (cornerHomRepresentation H M) (cornerHomRepresentation H P))
    (x : M) : moduleMapFromCornerHom H f x =
      (f.source (cornerDecomposition H M x).1 : P)+
      (f.target (cornerDecomposition H M x).2 : P) := rfl

theorem moduleMapFromCornerHom_extract (H : Subfield D) {M : Type*} {P : Type*}
    [AddCommGroup M] [Module (TriangularRing H)ᵐᵒᵖ M]
    [AddCommGroup P] [Module (TriangularRing H)ᵐᵒᵖ P]
    (g : M →ₗ[(TriangularRing H)ᵐᵒᵖ] P) :
    moduleMapFromCornerHom H (cornerHomRepresentationMap H g) = g := by
  apply LinearMap.ext
  intro x
  rw [moduleMapFromCornerHom_apply]
  change g (sourceCornerHom H 1 • x)+g (targetCornerHom H 1 • x) = g x
  rw [← g.map_add,← add_smul,corner_units_sum,one_smul]

theorem cornerHomRepresentationMap_reassemble (H : Subfield D) {M : Type*} {P : Type*}
    [AddCommGroup M] [Module (TriangularRing H)ᵐᵒᵖ M]
    [AddCommGroup P] [Module (TriangularRing H)ᵐᵒᵖ P]
    (f : HomRepresentationMorphism (cornerHomRepresentation H M) (cornerHomRepresentation H P)) :
    cornerHomRepresentationMap H (moduleMapFromCornerHom H f) = f := by
  apply HomRepresentationMorphism.ext
  · apply LinearMap.ext
    intro x
    apply Subtype.ext
    change moduleMapFromCornerHom H f (x : M) = (f.source x : P)
    rw [moduleMapFromCornerHom_apply,cornerDecomposition_source,map_zero]
    exact add_zero _
  · apply LinearMap.ext
    intro x
    apply Subtype.ext
    change moduleMapFromCornerHom H f (x : M) = (f.target x : P)
    rw [moduleMapFromCornerHom_apply,cornerDecomposition_target,map_zero]
    exact zero_add _

def cornerHomMapEquiv (H : Subfield D) (M : Type*) (P : Type*)
    [AddCommGroup M] [Module (TriangularRing H)ᵐᵒᵖ M]
    [AddCommGroup P] [Module (TriangularRing H)ᵐᵒᵖ P] :
    (M →ₗ[(TriangularRing H)ᵐᵒᵖ] P) ≃
      HomRepresentationMorphism (cornerHomRepresentation H M) (cornerHomRepresentation H P) where
  toFun := cornerHomRepresentationMap H
  invFun := moduleMapFromCornerHom H
  left_inv := moduleMapFromCornerHom_extract H
  right_inv := cornerHomRepresentationMap_reassemble H

theorem cornerHomMapEquiv_bijective (H : Subfield D) (M : Type*) (P : Type*)
    [AddCommGroup M] [Module (TriangularRing H)ᵐᵒᵖ M]
    [AddCommGroup P] [Module (TriangularRing H)ᵐᵒᵖ P] :
    Function.Bijective (cornerHomRepresentationMap H : (M →ₗ[(TriangularRing H)ᵐᵒᵖ] P) →
      HomRepresentationMorphism (cornerHomRepresentation H M) (cornerHomRepresentation H P)) :=
  (cornerHomMapEquiv H M P).bijective

end

end QuantumFlags

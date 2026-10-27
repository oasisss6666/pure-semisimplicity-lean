import QuantumFlags.BimoduleRepresentationRecovery
import QuantumFlags.TensorRepresentationCategory
import Mathlib.Algebra.Category.ModuleCat.Basic

namespace QuantumFlags
noncomputable section
open CategoryTheory
universe u v
variable (N : DivisionBimodule.{u})

def bimoduleRepresentationModuleFunctor : HomRepresentation.{u, max u v, max u v} N ⥤
    ModuleCat.{max u v} (BimoduleTriangularRing N)ᵐᵒᵖ where
  obj M := by
    letI := bimoduleModuleFromHomRepresentation N M
    exact ModuleCat.of _ (M.Source × M.Target)
  map {M P} f := by
    letI := bimoduleModuleFromHomRepresentation N M
    letI := bimoduleModuleFromHomRepresentation N P
    exact ModuleCat.ofHom (bimoduleHomRepresentationModuleMap N f)
  map_id M := by
    apply ModuleCat.hom_ext
    exact bimoduleHomRepresentationModuleMap_identity N M
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact bimoduleHomRepresentationModuleMap_compose N g f

def bimoduleModuleRepresentationFunctor : ModuleCat.{max u v} (BimoduleTriangularRing N)ᵐᵒᵖ ⥤
    HomRepresentation.{u, max u v, max u v} N where
  obj M := bimoduleCornerHomRepresentation N M
  map g := bimoduleCornerHomRepresentationMap N g.hom
  map_id M := bimoduleCornerHomRepresentationMap_identity N M
  map_comp f g := bimoduleCornerHomRepresentationMap_compose N g.hom f.hom

def bimoduleRepresentationUnitIso : 𝟭 (HomRepresentation.{u, max u v, max u v} N) ≅
    bimoduleRepresentationModuleFunctor N ⋙ bimoduleModuleRepresentationFunctor N :=
  NatIso.ofComponents (fun M => {
    hom := bimoduleHomRepresentationRecoveryInverse N M
    inv := bimoduleHomRepresentationRecovery N M
    hom_inv_id := bimoduleHomRepresentationRecovery_left_inverse N M
    inv_hom_id := bimoduleHomRepresentationRecovery_right_inverse N M })
    (by
      intro M P f
      apply HomRepresentationMorphism.ext
      · apply LinearMap.ext
        intro x
        apply Subtype.ext
        change (f.source x, 0) = (f.source x, f.target 0)
        rw [map_zero]
      · apply LinearMap.ext
        intro y
        apply Subtype.ext
        change (0, f.target y) = (f.source 0, f.target y)
        rw [map_zero])

def bimoduleModuleCounitIso :
    bimoduleModuleRepresentationFunctor N ⋙ bimoduleRepresentationModuleFunctor N ≅
      𝟭 (ModuleCat.{max u v} (BimoduleTriangularRing N)ᵐᵒᵖ) :=
  NatIso.ofComponents (fun M => (bimoduleCornerModuleEquiv N M).symm.toModuleIso)
    (by
      intro M P g
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change BimoduleSourceCorner N M × BimoduleTargetCorner N M at x
      change g.hom (x.1 : M) + g.hom (x.2 : M) = g.hom ((x.1 : M) + (x.2 : M))
      exact (g.hom.map_add _ _).symm)

/-- Arbitrary division-bimodule representations are actual right triangular-ring modules. -/
def bimoduleRepresentationEquivalence : HomRepresentation.{u, max u v, max u v} N ≌
    ModuleCat.{max u v} (BimoduleTriangularRing N)ᵐᵒᵖ :=
  CategoryTheory.Equivalence.mk (bimoduleRepresentationModuleFunctor N)
    (bimoduleModuleRepresentationFunctor N) (bimoduleRepresentationUnitIso N) (bimoduleModuleCounitIso N)

theorem bimoduleRepresentationEquivalence_exists :
    Nonempty (HomRepresentation.{u, max u v, max u v} N ≌
      ModuleCat.{max u v} (BimoduleTriangularRing N)ᵐᵒᵖ) :=
  ⟨bimoduleRepresentationEquivalence N⟩

def bimoduleTensorRepresentationEquivalence : TensorRepresentation.{u, max u v, max u v} N ≌
    ModuleCat.{max u v} (BimoduleTriangularRing N)ᵐᵒᵖ :=
  (tensorHomCategoryEquivalence N).trans (bimoduleRepresentationEquivalence N)

theorem bimoduleTensorRepresentationEquivalence_exists :
    Nonempty (TensorRepresentation.{u, max u v, max u v} N ≌
      ModuleCat.{max u v} (BimoduleTriangularRing N)ᵐᵒᵖ) :=
  ⟨bimoduleTensorRepresentationEquivalence N⟩

end
end QuantumFlags

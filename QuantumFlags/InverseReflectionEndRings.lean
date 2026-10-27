import QuantumFlags.ReflectionEndomorphismRings
import Mathlib.CategoryTheory.Conj

namespace QuantumFlags
noncomputable section
open CategoryTheory
universe u v

def isoEndRingEquiv {C : Type*} [Category C] [Preadditive C] {X Y : C} (α : X ≅ Y) :
    End X ≃+* End Y where
  toEquiv := α.conj.toEquiv
  map_mul' := α.conj.map_mul
  map_add' f g := by
    change α.inv ≫ (f+g) ≫ α.hom = (α.inv ≫ f ≫ α.hom)+(α.inv ≫ g ≫ α.hom)
    exact (congrArg (fun k : X ⟶ Y => α.inv ≫ k)
      (Preadditive.add_comp X X Y f g α.hom)).trans
      (Preadditive.comp_add Y X Y α.inv (f ≫ α.hom) (g ≫ α.hom))

variable (N : DivisionBimodule.{u}) [FiniteDimensional N.RightRingᵐᵒᵖ N.Space]
variable (L : SurjectiveDualTensorObjects.{u,v} N)

def inverseReflectionEndRingEquiv : End L ≃+* End ((inverseReflectionFunctor N).obj L) :=
  (isoEndRingEquiv ((reflectionCounitIso N).app L)).symm.trans
    (reflectionEndRingEquiv N ((inverseReflectionFunctor N).obj L)).symm

theorem inverseReflectionEndRingEquiv_exists :
    Nonempty (End L ≃+* End ((inverseReflectionFunctor N).obj L)) :=
  ⟨inverseReflectionEndRingEquiv N L⟩

end
end QuantumFlags

import QuantumFlags.TriangularRing
import QuantumFlags.LeftArtinianObstruction
import Mathlib.RingTheory.Artinian.Module
import Mathlib.Algebra.Module.FinitePresentation

namespace QuantumFlags

noncomputable section

variable {D : Type*} [DivisionRing D]

def diagonalElement (H : Subfield D) (h : H) (d : D) : TriangularRing H :=
  ⟨!![(h : D),0;0,d], by
    change (!![(h : D),0;0,d] : Matrix (Fin 2) (Fin 2) D) 1 0 = 0 ∧
      (!![(h : D),0;0,d] : Matrix (Fin 2) (Fin 2) D) 0 0 ∈ H
    simpa using h.property⟩

def diagonalRightHom (H : Subfield D) : Hᵐᵒᵖ × Dᵐᵒᵖ →+* (TriangularRing H)ᵐᵒᵖ where
  toFun r := MulOpposite.op (diagonalElement H r.1.unop r.2.unop)
  map_one' := by
    apply MulOpposite.unop_injective
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagonalElement]
  map_zero' := by
    apply MulOpposite.unop_injective
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagonalElement]
  map_add' r s := by
    apply MulOpposite.unop_injective
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagonalElement]
  map_mul' r s := by
    apply MulOpposite.unop_injective
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagonalElement, Matrix.mul_apply, Fin.sum_univ_two]

instance triangularDiagonalModule (H : Subfield D) :
    Module (Hᵐᵒᵖ × Dᵐᵒᵖ) (TriangularRing H) :=
  Module.compHom (TriangularRing H) (diagonalRightHom H)

instance triangularDiagonalModuleOpposite (H : Subfield D) :
    Module (Hᵐᵒᵖ × Dᵐᵒᵖ) (TriangularRing H)ᵐᵒᵖ :=
  Module.compHom (TriangularRing H)ᵐᵒᵖ (diagonalRightHom H)

instance triangularDiagonalTower (H : Subfield D) :
    IsScalarTower (Hᵐᵒᵖ × Dᵐᵒᵖ) (TriangularRing H)ᵐᵒᵖ (TriangularRing H) where
  smul_assoc r s M := by
    change M*(s.unop*(diagonalRightHom H r).unop) =
      (M*s.unop)*(diagonalRightHom H r).unop
    exact (mul_assoc M s.unop (diagonalRightHom H r).unop).symm

def cornerGenerators (H : Subfield D) : Fin 3 → TriangularRing H :=
  ![diagonalElement H 1 0, offDiagonal H 1, diagonalElement H 0 1]

theorem triangular_diagonal_span (H : Subfield D) :
    Submodule.span (Hᵐᵒᵖ × Dᵐᵒᵖ) (Set.range (cornerGenerators H)) = ⊤ := by
  apply top_unique
  intro M _
  let h : H := ⟨(M : Matrix (Fin 2) (Fin 2) D) 0 0,M.property.2⟩
  let a := (M : Matrix (Fin 2) (Fin 2) D) 0 1
  let b := (M : Matrix (Fin 2) (Fin 2) D) 1 1
  have he : M = ((MulOpposite.op h, 0) : Hᵐᵒᵖ × Dᵐᵒᵖ) • cornerGenerators H 0+
      ((0, MulOpposite.op a) : Hᵐᵒᵖ × Dᵐᵒᵖ) • cornerGenerators H 1+
      ((0, MulOpposite.op b) : Hᵐᵒᵖ × Dᵐᵒᵖ) • cornerGenerators H 2 := by
    apply Subtype.ext
    change (M : Matrix (Fin 2) (Fin 2) D) =
      ((cornerGenerators H 0 : Matrix (Fin 2) (Fin 2) D)*
        (diagonalElement H h 0 : Matrix (Fin 2) (Fin 2) D)+
      (cornerGenerators H 1 : Matrix (Fin 2) (Fin 2) D)*
        (diagonalElement H 0 a : Matrix (Fin 2) (Fin 2) D))+
      (cornerGenerators H 2 : Matrix (Fin 2) (Fin 2) D)*
        (diagonalElement H 0 b : Matrix (Fin 2) (Fin 2) D)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cornerGenerators,diagonalElement,offDiagonal,Matrix.mul_apply,
        Fin.sum_univ_two,h,a,b,M.property.1]
  rw [he]
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0,rfl⟩)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1,rfl⟩)
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨2,rfl⟩)

instance triangular_diagonal_finite (H : Subfield D) :
    Module.Finite (Hᵐᵒᵖ × Dᵐᵒᵖ) (TriangularRing H) := by
  apply Module.Finite.of_fg_top
  rw [← triangular_diagonal_span H]
  exact Submodule.fg_span (Set.finite_range (cornerGenerators H))

theorem triangular_right_artinian (H : Subfield D) :
    IsArtinian (TriangularRing H)ᵐᵒᵖ (TriangularRing H) :=
  isArtinian_of_tower (Hᵐᵒᵖ × Dᵐᵒᵖ) inferInstance

theorem actual_triangular_right_artinian :
    IsArtinian (TriangularRing (actualFlagSystem.H 1))ᵐᵒᵖ
      (TriangularRing (actualFlagSystem.H 1)) :=
  triangular_right_artinian (actualFlagSystem.H 1)

theorem triangular_right_noetherian (H : Subfield D) :
    IsNoetherian (TriangularRing H)ᵐᵒᵖ (TriangularRing H) :=
  isNoetherian_of_tower (Hᵐᵒᵖ × Dᵐᵒᵖ) inferInstance

theorem triangular_finite_presentation (H : Subfield D) (M : Type*) [AddCommGroup M]
    [Module (TriangularRing H)ᵐᵒᵖ M] [Module.Finite (TriangularRing H)ᵐᵒᵖ M] :
    Module.FinitePresentation (TriangularRing H)ᵐᵒᵖ M := by
  letI := triangular_right_noetherian H
  let e : TriangularRing H ≃ₗ[(TriangularRing H)ᵐᵒᵖ] (TriangularRing H)ᵐᵒᵖ := {
    toFun := MulOpposite.op
    invFun := MulOpposite.unop
    left_inv := MulOpposite.unop_op
    right_inv := MulOpposite.op_unop
    map_add' := MulOpposite.op_add
    map_smul' r x := rfl }
  letI : IsNoetherianRing (TriangularRing H)ᵐᵒᵖ := isNoetherian_of_linearEquiv e
  exact Module.finitePresentation_of_finite (TriangularRing H)ᵐᵒᵖ M

theorem actual_triangular_artinian_asymmetry :
    IsArtinian (TriangularRing (actualFlagSystem.H 1))ᵐᵒᵖ
      (TriangularRing (actualFlagSystem.H 1)) ∧
    ¬ IsArtinianRing (TriangularRing (actualFlagSystem.H 1)) :=
  ⟨actual_triangular_right_artinian,actual_triangular_not_left_artinian⟩

end

end QuantumFlags

import QuantumFlags.CornerFiniteness
import QuantumFlags.TriangularRepresentationAction

namespace QuantumFlags

noncomputable section

variable {D : Type*} [DivisionRing D]

@[simp] theorem source_offDiagonal_value (H : Subfield D) (x : D) :
    triangularSourceHom H (offDiagonal H x) = 0 := rfl

@[simp] theorem cross_offDiagonal_value (H : Subfield D) (x : D) :
    triangularCrossHom H (offDiagonal H x) = x := rfl

@[simp] theorem target_offDiagonal_value (H : Subfield D) (x : D) :
    triangularTargetHom H (offDiagonal H x) = 0 := rfl

theorem target_offDiagonal (H : Subfield D) (a : D) :
    targetCornerHom H (MulOpposite.op a)*MulOpposite.op (offDiagonal H 1) =
      MulOpposite.op (offDiagonal H a) := by
  apply MulOpposite.unop_injective
  change offDiagonal H 1*diagonalElement H 0 a = offDiagonal H a
  apply triangular_ext H <;> simp [triangularCrossHom_mul]

theorem target_offDiagonal_one (H : Subfield D) :
    targetCornerHom H 1*MulOpposite.op (offDiagonal H 1) =
      MulOpposite.op (offDiagonal H 1) := target_offDiagonal H 1

theorem offDiagonal_source (H : Subfield D) (a : Hᵐᵒᵖ) :
    MulOpposite.op (offDiagonal H 1)*sourceCornerHom H a =
      MulOpposite.op (offDiagonal H (a.unop : D)) := by
  apply MulOpposite.unop_injective
  change diagonalElement H a.unop 0*offDiagonal H 1 = offDiagonal H (a.unop : D)
  apply triangular_ext H <;> simp [triangularCrossHom_mul]

theorem offDiagonal_source_one (H : Subfield D) :
    MulOpposite.op (offDiagonal H 1)*sourceCornerHom H 1 =
      MulOpposite.op (offDiagonal H 1) := offDiagonal_source H 1

theorem source_corner_mul (H : Subfield D) (r : (TriangularRing H)ᵐᵒᵖ) :
    sourceCornerHom H 1*r = sourceCornerHom H ((triangularSourceHom H).op r) := by
  apply MulOpposite.unop_injective
  change r.unop*diagonalElement H 1 0 = diagonalElement H (triangularSourceHom H r.unop) 0
  apply triangular_ext H <;> simp [triangularCrossHom_mul]

theorem target_corner_mul (H : Subfield D) (r : (TriangularRing H)ᵐᵒᵖ) :
    targetCornerHom H 1*r = MulOpposite.op (offDiagonal H (triangularCrossHom H r.unop))+
      targetCornerHom H ((triangularTargetHom H).op r) := by
  apply MulOpposite.unop_injective
  change r.unop*diagonalElement H 0 1 =
    offDiagonal H (triangularCrossHom H r.unop)+diagonalElement H 0 (triangularTargetHom H r.unop)
  apply triangular_ext H <;> simp [triangularCrossHom_mul]

def cornerArrow (H : Subfield D) (M : Type*) [AddCommGroup M]
    [Module (TriangularRing H)ᵐᵒᵖ M] :
    letI := restrictedRightModule H (TargetCorner H M)
    SourceCorner H M →ₗ[Hᵐᵒᵖ] TargetCorner H M := by
  letI := restrictedRightModule H (TargetCorner H M)
  exact {
    toFun x := ⟨MulOpposite.op (offDiagonal H 1) • (x : M), by
      change targetCornerHom H 1 • (MulOpposite.op (offDiagonal H 1) • (x : M)) =
        MulOpposite.op (offDiagonal H 1) • (x : M)
      rw [← mul_smul,target_offDiagonal_one]⟩
    map_add' x y := by
      apply Subtype.ext
      exact smul_add (MulOpposite.op (offDiagonal H 1)) (x : M) (y : M)
    map_smul' a x := by
      apply Subtype.ext
      change MulOpposite.op (offDiagonal H 1) • (sourceCornerHom H a • (x : M)) =
        targetCornerHom H (MulOpposite.op (a.unop : D)) •
          (MulOpposite.op (offDiagonal H 1) • (x : M))
      rw [← mul_smul,← mul_smul,offDiagonal_source,target_offDiagonal] }

theorem cornerArrow_apply (H : Subfield D) (M : Type*) [AddCommGroup M]
    [Module (TriangularRing H)ᵐᵒᵖ M] (x : SourceCorner H M) :
    (cornerArrow H M x : M) = MulOpposite.op (offDiagonal H 1) • (x : M) := rfl

def cornerModuleEquiv (H : Subfield D) (M : Type*) [AddCommGroup M]
    [Module (TriangularRing H)ᵐᵒᵖ M] :
    letI := triangularModuleFromArrow H (SourceCorner H M) (TargetCorner H M) (cornerArrow H M)
    M ≃ₗ[(TriangularRing H)ᵐᵒᵖ] (SourceCorner H M × TargetCorner H M) := by
  letI := triangularModuleFromArrow H (SourceCorner H M) (TargetCorner H M) (cornerArrow H M)
  exact {
    toAddEquiv := cornerDecomposition H M
    map_smul' r x := by
      apply Prod.ext <;> apply Subtype.ext
      · change sourceCornerHom H 1 • (r • x) =
          sourceCornerHom H ((triangularSourceHom H).op r) • (sourceCornerHom H 1 • x)
        rw [← mul_smul,← mul_smul,source_corner_mul,← map_mul,mul_one]
      · change targetCornerHom H 1 • (r • x) =
          targetCornerHom H (MulOpposite.op (triangularCrossHom H r.unop)) •
            (MulOpposite.op (offDiagonal H 1) • (sourceCornerHom H 1 • x))+
          targetCornerHom H ((triangularTargetHom H).op r) • (targetCornerHom H 1 • x)
        rw [← mul_smul,target_corner_mul,add_smul]
        congr 1
        · rw [← mul_smul (MulOpposite.op (offDiagonal H 1)) (sourceCornerHom H 1),
            offDiagonal_source_one,← mul_smul,target_offDiagonal]
        · rw [← mul_smul,← map_mul,mul_one] }

theorem cornerModuleEquiv_apply (H : Subfield D) (M : Type*) [AddCommGroup M]
    [Module (TriangularRing H)ᵐᵒᵖ M] (x : M) :
    (((cornerModuleEquiv H M x).1 : M),((cornerModuleEquiv H M x).2 : M)) =
      (sourceCornerHom H 1 • x,targetCornerHom H 1 • x) := rfl

end

end QuantumFlags

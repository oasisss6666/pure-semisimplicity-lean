import QuantumFlags.TriangularCornerDecomposition

namespace QuantumFlags

noncomputable section

variable {D : Type*} [DivisionRing D]

abbrev SourceCorner (H : Subfield D) (M : Type*) [AddCommGroup M]
    [Module (TriangularRing H)ᵐᵒᵖ M] := cornerFixedGroup (sourceCornerHom H) M

abbrev TargetCorner (H : Subfield D) (M : Type*) [AddCommGroup M]
    [Module (TriangularRing H)ᵐᵒᵖ M] := cornerFixedGroup (targetCornerHom H) M

instance sourceCornerModule (H : Subfield D) (M : Type*) [AddCommGroup M]
    [Module (TriangularRing H)ᵐᵒᵖ M] : Module Hᵐᵒᵖ (SourceCorner H M) :=
  cornerFixedModule (sourceCornerHom H) M

instance targetCornerModule (H : Subfield D) (M : Type*) [AddCommGroup M]
    [Module (TriangularRing H)ᵐᵒᵖ M] : Module Dᵐᵒᵖ (TargetCorner H M) :=
  cornerFixedModule (targetCornerHom H) M

@[simp] theorem source_diagonal_value (H : Subfield D) (h : H) (d : D) :
    triangularSourceHom H (diagonalElement H h d) = h := rfl

@[simp] theorem cross_diagonal_value (H : Subfield D) (h : H) (d : D) :
    triangularCrossHom H (diagonalElement H h d) = 0 := rfl

@[simp] theorem target_diagonal_value (H : Subfield D) (h : H) (d : D) :
    triangularTargetHom H (diagonalElement H h d) = d := rfl

theorem source_regular_fixed (H : Subfield D)
    (x : SourceCorner H (TriangularRing H)ᵐᵒᵖ) :
    (x : (TriangularRing H)ᵐᵒᵖ).unop*diagonalElement H 1 0 =
      (x : (TriangularRing H)ᵐᵒᵖ).unop := by
  have h : sourceCornerHom H 1*(x : (TriangularRing H)ᵐᵒᵖ) = x := x.property
  exact congrArg MulOpposite.unop h

theorem source_regular_cross_zero (H : Subfield D)
    (x : SourceCorner H (TriangularRing H)ᵐᵒᵖ) :
    triangularCrossHom H (x : (TriangularRing H)ᵐᵒᵖ).unop = 0 := by
  have h := congrArg (triangularCrossHom H) (source_regular_fixed H x)
  rw [triangularCrossHom_mul,cross_diagonal_value,target_diagonal_value,
    mul_zero,mul_zero,add_zero] at h
  exact h.symm

theorem source_regular_target_zero (H : Subfield D)
    (x : SourceCorner H (TriangularRing H)ᵐᵒᵖ) :
    triangularTargetHom H (x : (TriangularRing H)ᵐᵒᵖ).unop = 0 := by
  have h := congrArg (triangularTargetHom H) (source_regular_fixed H x)
  rw [map_mul,target_diagonal_value,mul_zero] at h
  exact h.symm

def sourceRegularEquiv (H : Subfield D) :
    Hᵐᵒᵖ ≃ₗ[Hᵐᵒᵖ] SourceCorner H (TriangularRing H)ᵐᵒᵖ where
  toFun a := ⟨sourceCornerHom H a, by
    change sourceCornerHom H 1*sourceCornerHom H a = sourceCornerHom H a
    rw [← map_mul,one_mul]⟩
  invFun x := (triangularSourceHom H).op x
  left_inv a := rfl
  right_inv x := by
    apply Subtype.ext
    apply MulOpposite.unop_injective
    apply triangular_ext H
    · rfl
    · change 0 = triangularCrossHom H (x : (TriangularRing H)ᵐᵒᵖ).unop
      exact (source_regular_cross_zero H x).symm
    · change 0 = triangularTargetHom H (x : (TriangularRing H)ᵐᵒᵖ).unop
      exact (source_regular_target_zero H x).symm
  map_add' a b := Subtype.ext ((sourceCornerHom H).map_add a b)
  map_smul' a b := Subtype.ext ((sourceCornerHom H).map_mul a b)

theorem target_regular_fixed (H : Subfield D)
    (x : TargetCorner H (TriangularRing H)ᵐᵒᵖ) :
    (x : (TriangularRing H)ᵐᵒᵖ).unop*diagonalElement H 0 1 =
      (x : (TriangularRing H)ᵐᵒᵖ).unop := by
  have h : targetCornerHom H 1*(x : (TriangularRing H)ᵐᵒᵖ) = x := x.property
  exact congrArg MulOpposite.unop h

theorem target_regular_source_zero (H : Subfield D)
    (x : TargetCorner H (TriangularRing H)ᵐᵒᵖ) :
    triangularSourceHom H (x : (TriangularRing H)ᵐᵒᵖ).unop = 0 := by
  have h := congrArg (triangularSourceHom H) (target_regular_fixed H x)
  rw [map_mul,source_diagonal_value,mul_zero] at h
  exact h.symm

def targetRegularElement (H : Subfield D) (a : Fin 2 → Dᵐᵒᵖ) :
    TargetCorner H (TriangularRing H)ᵐᵒᵖ :=
  ⟨MulOpposite.op ⟨!![0,(a 0).unop;0,(a 1).unop], by
    change (!![0,(a 0).unop;0,(a 1).unop] : Matrix (Fin 2) (Fin 2) D) 1 0 = 0 ∧
      (!![0,(a 0).unop;0,(a 1).unop] : Matrix (Fin 2) (Fin 2) D) 0 0 ∈ H
    exact ⟨rfl,H.zero_mem⟩⟩, by
    change targetCornerHom H 1*MulOpposite.op _ = MulOpposite.op _
    apply MulOpposite.unop_injective
    apply Subtype.ext
    change (!![0,(a 0).unop;0,(a 1).unop] : Matrix (Fin 2) (Fin 2) D)*!![0,0;0,1] =
      !![0,(a 0).unop;0,(a 1).unop]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two]⟩

def targetRegularEquiv (H : Subfield D) :
    (Fin 2 → Dᵐᵒᵖ) ≃ₗ[Dᵐᵒᵖ] TargetCorner H (TriangularRing H)ᵐᵒᵖ where
  toFun := targetRegularElement H
  invFun x := ![MulOpposite.op (triangularCrossHom H (x : (TriangularRing H)ᵐᵒᵖ).unop),
    MulOpposite.op (triangularTargetHom H (x : (TriangularRing H)ᵐᵒᵖ).unop)]
  left_inv a := by funext i; fin_cases i <;> rfl
  right_inv x := by
    apply Subtype.ext
    apply MulOpposite.unop_injective
    apply triangular_ext H
    · change 0 = triangularSourceHom H (x : (TriangularRing H)ᵐᵒᵖ).unop
      exact (target_regular_source_zero H x).symm
    · rfl
    · rfl
  map_add' a b := by
    apply Subtype.ext
    apply MulOpposite.unop_injective
    apply Subtype.ext
    change (!![0,((a+b) 0).unop;0,((a+b) 1).unop] : Matrix (Fin 2) (Fin 2) D) =
      !![0,(a 0).unop;0,(a 1).unop]+!![0,(b 0).unop;0,(b 1).unop]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_smul' r a := by
    apply Subtype.ext
    apply MulOpposite.unop_injective
    apply Subtype.ext
    change (!![0,((r • a) 0).unop;0,((r • a) 1).unop] : Matrix (Fin 2) (Fin 2) D) =
      !![0,(a 0).unop;0,(a 1).unop]*!![0,0;0,r.unop]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two]

instance source_regular_finite (H : Subfield D) :
    FiniteDimensional Hᵐᵒᵖ (SourceCorner H (TriangularRing H)ᵐᵒᵖ) :=
  FiniteDimensional.of_injective (sourceRegularEquiv H).symm.toLinearMap
    (sourceRegularEquiv H).symm.injective

instance target_regular_finite (H : Subfield D) :
    FiniteDimensional Dᵐᵒᵖ (TargetCorner H (TriangularRing H)ᵐᵒᵖ) :=
  FiniteDimensional.of_injective (targetRegularEquiv H).symm.toLinearMap
    (targetRegularEquiv H).symm.injective

end

end QuantumFlags

import QuantumFlags.BimoduleTriangularRing

namespace QuantumFlags
noncomputable section
universe u
variable (N : DivisionBimodule.{u})

@[simp] theorem bimodule_source_offDiagonal (n : N.Space) :
    bimoduleSourceHom N (bimoduleOffDiagonal N n) = 0 := rfl
@[simp] theorem bimodule_target_offDiagonal (n : N.Space) :
    bimoduleTargetHom N (bimoduleOffDiagonal N n) = 0 := rfl
@[simp] theorem bimodule_cross_offDiagonal (n : N.Space) :
    bimoduleCrossHom N (bimoduleOffDiagonal N n) = n := rfl

def bimoduleOffDiagonalAddHom : N.Space →+ (BimoduleTriangularRing N)ᵐᵒᵖ where
  toFun n := MulOpposite.op (bimoduleOffDiagonal N n)
  map_zero' := rfl
  map_add' n m := by
    apply MulOpposite.unop_injective
    apply bimodule_triangular_ext N <;> simp

theorem bimodule_target_offDiagonal_mul (b : N.RightRingᵐᵒᵖ) (n : N.Space) :
    bimoduleTargetCornerHom N b * MulOpposite.op (bimoduleOffDiagonal N n) =
      MulOpposite.op (bimoduleOffDiagonal N (b • n)) := by
  apply MulOpposite.unop_injective
  change bimoduleOffDiagonal N n * bimoduleDiagonal N 0 b.unop = _
  apply bimodule_triangular_ext N <;> simp [bimodule_cross_mul]

theorem bimodule_offDiagonal_source_mul (a : N.LeftRingᵐᵒᵖ) (n : N.Space) :
    MulOpposite.op (bimoduleOffDiagonal N n) * bimoduleSourceCornerHom N a =
      MulOpposite.op (bimoduleOffDiagonal N (a.unop • n)) := by
  apply MulOpposite.unop_injective
  change bimoduleDiagonal N a.unop 0 * bimoduleOffDiagonal N n = _
  apply bimodule_triangular_ext N <;> simp [bimodule_cross_mul]

theorem bimodule_target_offDiagonal_one (n : N.Space) :
    bimoduleTargetCornerHom N 1 * MulOpposite.op (bimoduleOffDiagonal N n) =
      MulOpposite.op (bimoduleOffDiagonal N n) := by
  simpa only [one_smul] using bimodule_target_offDiagonal_mul N 1 n

theorem bimodule_offDiagonal_source_one (n : N.Space) :
    MulOpposite.op (bimoduleOffDiagonal N n) * bimoduleSourceCornerHom N 1 =
      MulOpposite.op (bimoduleOffDiagonal N n) := by
  simpa only [MulOpposite.unop_one, one_smul] using bimodule_offDiagonal_source_mul N 1 n

theorem bimodule_source_corner_mul (r : (BimoduleTriangularRing N)ᵐᵒᵖ) :
    bimoduleSourceCornerHom N 1 * r =
      bimoduleSourceCornerHom N ((bimoduleSourceHom N).op r) := by
  apply MulOpposite.unop_injective
  change r.unop * bimoduleDiagonal N 1 0 =
    bimoduleDiagonal N (bimoduleSourceHom N r.unop) 0
  apply bimodule_triangular_ext N <;> simp [bimodule_cross_mul]

theorem bimodule_target_corner_mul (r : (BimoduleTriangularRing N)ᵐᵒᵖ) :
    bimoduleTargetCornerHom N 1 * r =
      MulOpposite.op (bimoduleOffDiagonal N (bimoduleCrossHom N r.unop)) +
        bimoduleTargetCornerHom N ((bimoduleTargetHom N).op r) := by
  apply MulOpposite.unop_injective
  change r.unop * bimoduleDiagonal N 0 1 =
    bimoduleOffDiagonal N (bimoduleCrossHom N r.unop) +
      bimoduleDiagonal N 0 (bimoduleTargetHom N r.unop)
  apply bimodule_triangular_ext N <;> simp [bimodule_cross_mul]

theorem bimodule_source_target_zero :
    bimoduleSourceCornerHom N 1 * bimoduleTargetCornerHom N 1 = 0 := by
  change bimoduleDiagonalRightHom N (1,0) * bimoduleDiagonalRightHom N (0,1) = 0
  have h : ((1,0) : N.LeftRingᵐᵒᵖ × N.RightRingᵐᵒᵖ) * (0,1) = 0 := by ext <;> simp
  rw [← map_mul, h, map_zero]

theorem bimodule_target_source_zero :
    bimoduleTargetCornerHom N 1 * bimoduleSourceCornerHom N 1 = 0 := by
  change bimoduleDiagonalRightHom N (0,1) * bimoduleDiagonalRightHom N (1,0) = 0
  have h : ((0,1) : N.LeftRingᵐᵒᵖ × N.RightRingᵐᵒᵖ) * (1,0) = 0 := by ext <;> simp
  rw [← map_mul, h, map_zero]

abbrev BimoduleSourceCorner (M : Type*) [AddCommGroup M]
    [Module (BimoduleTriangularRing N)ᵐᵒᵖ M] := cornerFixedGroup (bimoduleSourceCornerHom N) M
abbrev BimoduleTargetCorner (M : Type*) [AddCommGroup M]
    [Module (BimoduleTriangularRing N)ᵐᵒᵖ M] := cornerFixedGroup (bimoduleTargetCornerHom N) M

instance bimoduleSourceCornerModule (M : Type*) [AddCommGroup M]
    [Module (BimoduleTriangularRing N)ᵐᵒᵖ M] : Module N.LeftRingᵐᵒᵖ (BimoduleSourceCorner N M) :=
  cornerFixedModule (bimoduleSourceCornerHom N) M
instance bimoduleTargetCornerModule (M : Type*) [AddCommGroup M]
    [Module (BimoduleTriangularRing N)ᵐᵒᵖ M] : Module N.RightRingᵐᵒᵖ (BimoduleTargetCorner N M) :=
  cornerFixedModule (bimoduleTargetCornerHom N) M

def bimoduleCornerDecomposition (M : Type*) [AddCommGroup M]
    [Module (BimoduleTriangularRing N)ᵐᵒᵖ M] :
    M ≃+ BimoduleSourceCorner N M × BimoduleTargetCorner N M where
  toFun x := (⟨bimoduleSourceCornerHom N 1 • x, corner_projection_idempotent _ M x⟩,
    ⟨bimoduleTargetCornerHom N 1 • x, corner_projection_idempotent _ M x⟩)
  invFun p := (p.1 : M) + (p.2 : M)
  left_inv x := by
    change bimoduleSourceCornerHom N 1 • x + bimoduleTargetCornerHom N 1 • x = x
    rw [← add_smul, bimodule_corner_units_sum, one_smul]
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      change bimoduleSourceCornerHom N 1 • ((p.1 : M) + (p.2 : M)) = (p.1 : M)
      have hc : bimoduleSourceCornerHom N 1 • (p.2 : M) = 0 := by
        rw [← p.2.property, ← mul_smul, bimodule_source_target_zero, zero_smul]
      rw [smul_add, p.1.property, hc, add_zero]
    · apply Subtype.ext
      change bimoduleTargetCornerHom N 1 • ((p.1 : M) + (p.2 : M)) = (p.2 : M)
      have hc : bimoduleTargetCornerHom N 1 • (p.1 : M) = 0 := by
        rw [← p.1.property, ← mul_smul, bimodule_target_source_zero, zero_smul]
      rw [smul_add, hc, p.2.property, zero_add]
  map_add' x y := by
    apply Prod.ext <;> apply Subtype.ext
    · exact smul_add (bimoduleSourceCornerHom N 1) x y
    · exact smul_add (bimoduleTargetCornerHom N 1) x y

theorem bimoduleCornerDecomposition_components (M : Type*) [AddCommGroup M]
    [Module (BimoduleTriangularRing N)ᵐᵒᵖ M] (x : M) :
    (((bimoduleCornerDecomposition N M x).1 : M),
      ((bimoduleCornerDecomposition N M x).2 : M)) =
      (bimoduleSourceCornerHom N 1 • x, bimoduleTargetCornerHom N 1 • x) := rfl

end
end QuantumFlags

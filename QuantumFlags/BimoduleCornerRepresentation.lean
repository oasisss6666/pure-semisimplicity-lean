import QuantumFlags.BimoduleCornerIdentities
import QuantumFlags.BimoduleRepresentationAction

namespace QuantumFlags
noncomputable section
universe u
variable (N : DivisionBimodule.{u})

@[instance_reducible]
def bimoduleModuleFromHomRepresentation (M : HomRepresentation N) :
    Module (BimoduleTriangularRing N)ᵐᵒᵖ (M.Source × M.Target) :=
  bimoduleModuleFromArrow N M.Source M.Target M.arrow

abbrev bimoduleCornerHomRepresentation (M : Type*) [AddCommGroup M]
    [Module (BimoduleTriangularRing N)ᵐᵒᵖ M] : HomRepresentation N where
  Source := BimoduleSourceCorner N M
  Target := BimoduleTargetCorner N M
  arrow := by
    letI := rightHomModule N (BimoduleTargetCorner N M)
    exact {
      toFun x := {
        toFun n := ⟨MulOpposite.op (bimoduleOffDiagonal N n) • (x : M), by
          change bimoduleTargetCornerHom N 1 •
            (MulOpposite.op (bimoduleOffDiagonal N n) • (x : M)) =
              MulOpposite.op (bimoduleOffDiagonal N n) • (x : M)
          rw [← mul_smul, bimodule_target_offDiagonal_one]⟩
        map_add' n m := by
          apply Subtype.ext
          change bimoduleOffDiagonalAddHom N (n+m) • (x : M) =
            bimoduleOffDiagonalAddHom N n • (x : M) +
              bimoduleOffDiagonalAddHom N m • (x : M)
          rw [map_add, add_smul]
        map_smul' b n := by
          apply Subtype.ext
          change MulOpposite.op (bimoduleOffDiagonal N (b • n)) • (x : M) =
            bimoduleTargetCornerHom N b • (MulOpposite.op (bimoduleOffDiagonal N n) • (x : M))
          rw [← mul_smul, bimodule_target_offDiagonal_mul] }
      map_add' x y := by
        apply LinearMap.ext
        intro n
        apply Subtype.ext
        exact smul_add (MulOpposite.op (bimoduleOffDiagonal N n)) (x : M) (y : M)
      map_smul' a x := by
        apply LinearMap.ext
        intro n
        apply Subtype.ext
        change MulOpposite.op (bimoduleOffDiagonal N n) • (bimoduleSourceCornerHom N a • (x : M)) =
          MulOpposite.op (bimoduleOffDiagonal N (a.unop • n)) • (x : M)
        rw [← mul_smul, bimodule_offDiagonal_source_mul] }

theorem bimoduleCornerHomRepresentation_arrow_apply (M : Type*) [AddCommGroup M]
    [Module (BimoduleTriangularRing N)ᵐᵒᵖ M] (x : BimoduleSourceCorner N M) (n : N.Space) :
    ((bimoduleCornerHomRepresentation N M).arrow x n : M) =
      MulOpposite.op (bimoduleOffDiagonal N n) • (x : M) := rfl

def bimoduleCornerModuleEquiv (M : Type*) [AddCommGroup M]
    [Module (BimoduleTriangularRing N)ᵐᵒᵖ M] :
    letI := bimoduleModuleFromHomRepresentation N (bimoduleCornerHomRepresentation N M)
    M ≃ₗ[(BimoduleTriangularRing N)ᵐᵒᵖ]
      (BimoduleSourceCorner N M × BimoduleTargetCorner N M) := by
  letI := bimoduleModuleFromHomRepresentation N (bimoduleCornerHomRepresentation N M)
  exact {
    toAddEquiv := bimoduleCornerDecomposition N M
    map_smul' r x := by
      apply Prod.ext <;> apply Subtype.ext
      · change bimoduleSourceCornerHom N 1 • (r • x) =
          bimoduleSourceCornerHom N ((bimoduleSourceHom N).op r) •
            (bimoduleSourceCornerHom N 1 • x)
        rw [← mul_smul, ← mul_smul, bimodule_source_corner_mul, ← map_mul, mul_one]
      · change bimoduleTargetCornerHom N 1 • (r • x) =
          MulOpposite.op (bimoduleOffDiagonal N (bimoduleCrossHom N r.unop)) •
            (bimoduleSourceCornerHom N 1 • x) +
          bimoduleTargetCornerHom N ((bimoduleTargetHom N).op r) •
            (bimoduleTargetCornerHom N 1 • x)
        rw [← mul_smul, bimodule_target_corner_mul, add_smul]
        congr 1
        · rw [← mul_smul, bimodule_offDiagonal_source_one]
        · rw [← mul_smul, ← map_mul, mul_one] }

theorem bimoduleCornerModuleEquiv_apply (M : Type*) [AddCommGroup M]
    [Module (BimoduleTriangularRing N)ᵐᵒᵖ M] (x : M) :
    (((bimoduleCornerModuleEquiv N M x).1 : M), ((bimoduleCornerModuleEquiv N M x).2 : M)) =
      (bimoduleSourceCornerHom N 1 • x, bimoduleTargetCornerHom N 1 • x) := rfl

end
end QuantumFlags

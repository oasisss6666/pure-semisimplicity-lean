import QuantumFlags.HomRepresentations

namespace QuantumFlags

noncomputable section

universe u

variable {D : Type u} [DivisionRing D]

@[instance_reducible]
def restrictedRightModule (H : Subfield D) (Y : Type*) [AddCommGroup Y] [Module Dᵐᵒᵖ Y] :
    Module Hᵐᵒᵖ Y := Module.compHom Y H.subtype.op

def ambientHomEvaluationEquiv (H : Subfield D) (Y : Type*) [AddCommGroup Y]
    [Module Dᵐᵒᵖ Y] :
    letI := restrictedRightModule H Y
    letI := rightHomModule (ambientBimodule H) Y
    BimoduleRightHom (ambientBimodule H) Y ≃ₗ[Hᵐᵒᵖ] Y := by
  letI := restrictedRightModule H Y
  letI := rightHomModule (ambientBimodule H) Y
  exact {
    toFun φ := φ 1
    invFun y := {
      toFun x := MulOpposite.op x • y
      map_add' x z := by
        change (MulOpposite.op x+MulOpposite.op z) • y =
          MulOpposite.op x • y+MulOpposite.op z • y
        rw [add_smul]
      map_smul' r x := by
        change MulOpposite.op (x*r.unop) • y = r • (MulOpposite.op x • y)
        rw [MulOpposite.op_mul,MulOpposite.op_unop,mul_smul] }
    left_inv φ := by
      apply LinearMap.ext
      intro x
      have h := φ.map_smul (MulOpposite.op x) 1
      change φ (1*x) = MulOpposite.op x • φ 1 at h
      simpa using h.symm
    right_inv y := one_smul Dᵐᵒᵖ y
    map_add' φ ψ := rfl
    map_smul' r φ := by
      change φ ((r.unop : D)*1) = MulOpposite.op (r.unop : D) • φ 1
      have h := φ.map_smul (MulOpposite.op (r.unop : D)) 1
      change φ (1*(r.unop : D)) = MulOpposite.op (r.unop : D) • φ 1 at h
      simpa using h }

theorem ambientHomEvaluationEquiv_apply (H : Subfield D) (Y : Type*) [AddCommGroup Y]
    [Module Dᵐᵒᵖ Y] (φ : BimoduleRightHom (ambientBimodule H) Y) :
    ambientHomEvaluationEquiv H Y φ = φ 1 := rfl

theorem ambientHomEvaluationEquiv_symm_apply (H : Subfield D) (Y : Type*) [AddCommGroup Y]
    [Module Dᵐᵒᵖ Y] (y : Y) (x : D) :
    (ambientHomEvaluationEquiv H Y).symm y x = MulOpposite.op x • y := rfl

def ambientRepresentationArrow (H : Subfield D) (M : HomRepresentation (ambientBimodule H)) :
    letI : Module Hᵐᵒᵖ M.Source := M.sourceModule
    letI : Module Dᵐᵒᵖ M.Target := M.targetModule
    letI := restrictedRightModule H M.Target
    M.Source →ₗ[Hᵐᵒᵖ] M.Target := by
  letI : Module Hᵐᵒᵖ M.Source := M.sourceModule
  letI : Module Dᵐᵒᵖ M.Target := M.targetModule
  letI := restrictedRightModule H M.Target
  letI := rightHomModule (ambientBimodule H) M.Target
  exact (ambientHomEvaluationEquiv H M.Target).toLinearMap.comp M.arrow

theorem ambientRepresentationArrow_apply (H : Subfield D)
    (M : HomRepresentation (ambientBimodule H)) (x : M.Source) :
    ambientRepresentationArrow H M x = M.arrow x 1 := rfl

end

end QuantumFlags

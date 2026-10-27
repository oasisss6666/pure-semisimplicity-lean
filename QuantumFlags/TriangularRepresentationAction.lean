import QuantumFlags.TriangularCoordinates
import QuantumFlags.AmbientHomEvaluation

namespace QuantumFlags

noncomputable section

variable {D : Type*} [DivisionRing D]

/-- The actual right action `(x,y)[h,a;0,b] = (xh,theta(x)a+yb)`. -/
@[instance_reducible]
def triangularModuleFromArrow (H : Subfield D) (X : Type*) (Y : Type*) [AddCommGroup X]
    [Module Hᵐᵒᵖ X] [AddCommGroup Y] [Module Dᵐᵒᵖ Y]
    (θ : letI := restrictedRightModule H Y
      X →ₗ[Hᵐᵒᵖ] Y) : Module (TriangularRing H)ᵐᵒᵖ (X × Y) where
  smul r p := ((triangularSourceHom H).op r • p.1,
    MulOpposite.op (triangularCrossHom H r.unop) • θ p.1+
      (triangularTargetHom H).op r • p.2)
  one_smul p := by
    apply Prod.ext
    · change (triangularSourceHom H).op 1 • p.1 = p.1
      rw [map_one,one_smul]
    · change MulOpposite.op (triangularCrossHom H 1) • θ p.1+
        (triangularTargetHom H).op 1 • p.2 = p.2
      rw [triangularCrossHom_one,map_one]
      simp
  zero_smul p := by
    apply Prod.ext
    · change (triangularSourceHom H).op 0 • p.1 = 0
      rw [map_zero,zero_smul]
    · change MulOpposite.op (triangularCrossHom H 0) • θ p.1+
        (triangularTargetHom H).op 0 • p.2 = 0
      rw [map_zero,map_zero]
      simp
  smul_zero r := by
    apply Prod.ext
    · exact smul_zero ((triangularSourceHom H).op r)
    · change MulOpposite.op (triangularCrossHom H r.unop) • θ 0+
        (triangularTargetHom H).op r • (0 : Y) = 0
      rw [map_zero,smul_zero,smul_zero,add_zero]
  smul_add r p q := by
    apply Prod.ext
    · exact smul_add ((triangularSourceHom H).op r) p.1 q.1
    · change MulOpposite.op (triangularCrossHom H r.unop) • θ (p.1+q.1)+
        (triangularTargetHom H).op r • (p.2+q.2) =
        (MulOpposite.op (triangularCrossHom H r.unop) • θ p.1+
          (triangularTargetHom H).op r • p.2)+
        (MulOpposite.op (triangularCrossHom H r.unop) • θ q.1+
          (triangularTargetHom H).op r • q.2)
      rw [map_add,smul_add,smul_add]
      abel
  add_smul r s p := by
    apply Prod.ext
    · change (triangularSourceHom H).op (r+s) • p.1 =
        (triangularSourceHom H).op r • p.1+(triangularSourceHom H).op s • p.1
      rw [map_add,add_smul]
    · change MulOpposite.op (triangularCrossHom H (r+s).unop) • θ p.1+
        (triangularTargetHom H).op (r+s) • p.2 =
        (MulOpposite.op (triangularCrossHom H r.unop) • θ p.1+
          (triangularTargetHom H).op r • p.2)+
        (MulOpposite.op (triangularCrossHom H s.unop) • θ p.1+
          (triangularTargetHom H).op s • p.2)
      simp only [MulOpposite.unop_add,map_add,MulOpposite.op_add,add_smul]
      abel
  mul_smul r s p := by
    apply Prod.ext
    · change (triangularSourceHom H).op (r*s) • p.1 =
        (triangularSourceHom H).op r • ((triangularSourceHom H).op s • p.1)
      rw [map_mul,mul_smul]
    · have hθ : θ ((triangularSourceHom H).op s • p.1) =
          MulOpposite.op ((triangularSourceHom H s.unop : H) : D) • θ p.1 := by
        letI := restrictedRightModule H Y
        have hh := θ.map_smul ((triangularSourceHom H).op s) p.1
        exact hh
      have hδ : MulOpposite.op (triangularCrossHom H (r*s).unop) =
          MulOpposite.op (triangularCrossHom H r.unop)*
            MulOpposite.op ((triangularSourceHom H s.unop : H) : D)+
          (triangularTargetHom H).op r*MulOpposite.op (triangularCrossHom H s.unop) := by
        rw [MulOpposite.unop_mul,triangularCrossHom_mul,MulOpposite.op_add,
          MulOpposite.op_mul,MulOpposite.op_mul]
        rfl
      change MulOpposite.op (triangularCrossHom H (r*s).unop) • θ p.1+
        (triangularTargetHom H).op (r*s) • p.2 =
        MulOpposite.op (triangularCrossHom H r.unop) •
          θ ((triangularSourceHom H).op s • p.1)+
        (triangularTargetHom H).op r •
          (MulOpposite.op (triangularCrossHom H s.unop) • θ p.1+
            (triangularTargetHom H).op s • p.2)
      rw [hδ,hθ,map_mul]
      simp only [add_smul,mul_smul,smul_add]
      abel

theorem triangular_action_formula (H : Subfield D) (X : Type*) (Y : Type*) [AddCommGroup X]
    [Module Hᵐᵒᵖ X] [AddCommGroup Y] [Module Dᵐᵒᵖ Y]
    (θ : letI := restrictedRightModule H Y
      X →ₗ[Hᵐᵒᵖ] Y) (r : (TriangularRing H)ᵐᵒᵖ) (p : X × Y) :
    letI := triangularModuleFromArrow H X Y θ
    r • p = ((triangularSourceHom H).op r • p.1,
      MulOpposite.op (triangularCrossHom H r.unop) • θ p.1+
        (triangularTargetHom H).op r • p.2) := rfl

@[instance_reducible]
def moduleFromHomRepresentation (H : Subfield D)
    (M : HomRepresentation (ambientBimodule H)) :
    Module (TriangularRing H)ᵐᵒᵖ (M.Source × M.Target) := by
  letI : Module Hᵐᵒᵖ M.Source := M.sourceModule
  letI : Module Dᵐᵒᵖ M.Target := M.targetModule
  exact triangularModuleFromArrow H M.Source M.Target (ambientRepresentationArrow H M)

theorem homRepresentation_rightModule_exists (H : Subfield D)
    (M : HomRepresentation (ambientBimodule H)) :
    Nonempty (Module (TriangularRing H)ᵐᵒᵖ (M.Source × M.Target)) :=
  ⟨moduleFromHomRepresentation H M⟩

end

end QuantumFlags

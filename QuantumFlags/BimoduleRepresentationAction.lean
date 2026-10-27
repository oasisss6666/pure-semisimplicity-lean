import QuantumFlags.BimoduleTriangularRing
import QuantumFlags.HomRepresentations

namespace QuantumFlags
noncomputable section
universe u

@[instance_reducible]
def bimoduleModuleFromArrow (N : DivisionBimodule.{u}) (X Y : Type*)
    [AddCommGroup X] [Module N.LeftRingᵐᵒᵖ X]
    [AddCommGroup Y] [Module N.RightRingᵐᵒᵖ Y]
    (β : letI := rightHomModule N Y; X →ₗ[N.LeftRingᵐᵒᵖ] BimoduleRightHom N Y) :
    Module (BimoduleTriangularRing N)ᵐᵒᵖ (X × Y) where
  smul r p := ((bimoduleSourceHom N).op r • p.1,
    β p.1 (bimoduleCrossHom N r.unop)+(bimoduleTargetHom N).op r • p.2)
  one_smul p := by
    apply Prod.ext
    · change (bimoduleSourceHom N).op 1 • p.1 = p.1
      rw [map_one,one_smul]
    · change β p.1 0+(bimoduleTargetHom N).op 1 • p.2 = p.2
      rw [map_zero,map_one,one_smul,zero_add]
  zero_smul p := by
    apply Prod.ext
    · change (bimoduleSourceHom N).op 0 • p.1 = 0
      rw [map_zero,zero_smul]
    · change β p.1 0+(bimoduleTargetHom N).op 0 • p.2 = 0
      rw [map_zero,map_zero,zero_smul,add_zero]
  smul_zero r := by
    apply Prod.ext
    · exact smul_zero _
    · change β 0 (bimoduleCrossHom N r.unop)+(bimoduleTargetHom N).op r • (0 : Y) = 0
      simp
  smul_add r p q := by
    apply Prod.ext
    · exact smul_add _ _ _
    · change β (p.1+q.1) (bimoduleCrossHom N r.unop)+
        (bimoduleTargetHom N).op r • (p.2+q.2) = _
      rw [map_add,smul_add]
      change (β p.1 (bimoduleCrossHom N r.unop)+β q.1 (bimoduleCrossHom N r.unop))+
        ((bimoduleTargetHom N).op r • p.2+(bimoduleTargetHom N).op r • q.2) =
          (β p.1 (bimoduleCrossHom N r.unop)+(bimoduleTargetHom N).op r • p.2)+
          (β q.1 (bimoduleCrossHom N r.unop)+(bimoduleTargetHom N).op r • q.2)
      abel
  add_smul r s p := by
    apply Prod.ext
    · change (bimoduleSourceHom N).op (r+s) • p.1 =
        (bimoduleSourceHom N).op r • p.1+(bimoduleSourceHom N).op s • p.1
      rw [map_add,add_smul]
    · change β p.1 (bimoduleCrossHom N (r+s).unop)+(bimoduleTargetHom N).op (r+s) • p.2 = _
      simp only [MulOpposite.unop_add,map_add,add_smul]
      change (β p.1 (bimoduleCrossHom N r.unop)+β p.1 (bimoduleCrossHom N s.unop))+
        ((bimoduleTargetHom N).op r • p.2+(bimoduleTargetHom N).op s • p.2) =
          (β p.1 (bimoduleCrossHom N r.unop)+(bimoduleTargetHom N).op r • p.2)+
          (β p.1 (bimoduleCrossHom N s.unop)+(bimoduleTargetHom N).op s • p.2)
      abel
  mul_smul r s p := by
    apply Prod.ext
    · change (bimoduleSourceHom N).op (r*s) • p.1 =
        (bimoduleSourceHom N).op r • ((bimoduleSourceHom N).op s • p.1)
      rw [map_mul,mul_smul]
    · have hβ : β ((bimoduleSourceHom N).op s • p.1) (bimoduleCrossHom N r.unop) =
          β p.1 (bimoduleSourceHom N s.unop • bimoduleCrossHom N r.unop) := by
        letI := rightHomModule N Y
        have h := β.map_smul ((bimoduleSourceHom N).op s) p.1
        exact LinearMap.congr_fun h (bimoduleCrossHom N r.unop)
      change β p.1 (bimoduleCrossHom N (r*s).unop)+(bimoduleTargetHom N).op (r*s) • p.2 =
        β ((bimoduleSourceHom N).op s • p.1) (bimoduleCrossHom N r.unop)+
        (bimoduleTargetHom N).op r •
          (β p.1 (bimoduleCrossHom N s.unop)+(bimoduleTargetHom N).op s • p.2)
      rw [MulOpposite.unop_mul,bimodule_cross_mul,map_add,
        (β p.1).map_smul (MulOpposite.op (bimoduleTargetHom N r.unop))
          (bimoduleCrossHom N s.unop),hβ,map_mul]
      simp only [smul_add,mul_smul]
      change (β p.1 (bimoduleSourceHom N s.unop • bimoduleCrossHom N r.unop)+
          (bimoduleTargetHom N).op r • β p.1 (bimoduleCrossHom N s.unop))+
          (bimoduleTargetHom N).op r • ((bimoduleTargetHom N).op s • p.2) =
        β p.1 (bimoduleSourceHom N s.unop • bimoduleCrossHom N r.unop)+
          ((bimoduleTargetHom N).op r • β p.1 (bimoduleCrossHom N s.unop)+
            (bimoduleTargetHom N).op r • ((bimoduleTargetHom N).op s • p.2))
      exact add_assoc _ _ _

theorem bimodule_representation_action (N : DivisionBimodule.{u}) (X Y : Type*)
    [AddCommGroup X] [Module N.LeftRingᵐᵒᵖ X]
    [AddCommGroup Y] [Module N.RightRingᵐᵒᵖ Y]
    (β : letI := rightHomModule N Y; X →ₗ[N.LeftRingᵐᵒᵖ] BimoduleRightHom N Y)
    (r : (BimoduleTriangularRing N)ᵐᵒᵖ) (p : X × Y) :
    letI := bimoduleModuleFromArrow N X Y β
    r • p = ((bimoduleSourceHom N).op r • p.1,
      β p.1 (bimoduleCrossHom N r.unop)+(bimoduleTargetHom N).op r • p.2) := rfl

end
end QuantumFlags

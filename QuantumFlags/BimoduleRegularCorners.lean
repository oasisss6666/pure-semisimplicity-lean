import QuantumFlags.BimoduleTriangularRing

namespace QuantumFlags

noncomputable section

universe u

def bimoduleSourceRegularEquiv (N : DivisionBimodule.{u}) :
    letI := cornerFixedModule (bimoduleSourceCornerHom N) (BimoduleTriangularRing N)ᵐᵒᵖ
    N.LeftRingᵐᵒᵖ ≃ₗ[N.LeftRingᵐᵒᵖ]
      cornerFixedGroup (bimoduleSourceCornerHom N) (BimoduleTriangularRing N)ᵐᵒᵖ := by
  letI := cornerFixedModule (bimoduleSourceCornerHom N) (BimoduleTriangularRing N)ᵐᵒᵖ
  exact {
    toFun a := ⟨bimoduleSourceCornerHom N a,by
      change bimoduleSourceCornerHom N 1*bimoduleSourceCornerHom N a = bimoduleSourceCornerHom N a
      rw [← map_mul,one_mul]⟩
    invFun x := (bimoduleSourceHom N).op x
    left_inv _ := rfl
    right_inv x := by
      have hx : bimoduleSourceCornerHom N 1*(x : (BimoduleTriangularRing N)ᵐᵒᵖ) = x := x.property
      have hu := congrArg MulOpposite.unop hx
      apply Subtype.ext
      apply MulOpposite.unop_injective
      apply bimodule_triangular_ext N
      · rfl
      · change (0 : N.RightRing) = bimoduleTargetHom N (x : (BimoduleTriangularRing N)ᵐᵒᵖ).unop
        have ht := congrArg (bimoduleTargetHom N) hu
        change bimoduleTargetHom N (x : (BimoduleTriangularRing N)ᵐᵒᵖ).unop*0 =
          bimoduleTargetHom N (x : (BimoduleTriangularRing N)ᵐᵒᵖ).unop at ht
        simpa using ht
      · change (0 : N.Space) = bimoduleCrossHom N (x : (BimoduleTriangularRing N)ᵐᵒᵖ).unop
        have hn := congrArg (bimoduleCrossHom N) hu
        change bimoduleSourceHom N (x : (BimoduleTriangularRing N)ᵐᵒᵖ).unop • (0 : N.Space)+
          (0 : N.RightRingᵐᵒᵖ) • bimoduleCrossHom N (x : (BimoduleTriangularRing N)ᵐᵒᵖ).unop =
          bimoduleCrossHom N (x : (BimoduleTriangularRing N)ᵐᵒᵖ).unop at hn
        simpa using hn
    map_add' a b := Subtype.ext ((bimoduleSourceCornerHom N).map_add a b)
    map_smul' a b := Subtype.ext ((bimoduleSourceCornerHom N).map_mul a b) }

def bimoduleTargetRegularElement (N : DivisionBimodule.{u}) (p : N.Space × N.RightRingᵐᵒᵖ) :
    cornerFixedGroup (bimoduleTargetCornerHom N) (BimoduleTriangularRing N)ᵐᵒᵖ := by
  let r : BimoduleTriangularRing N := ((0,p.2.unop),p.1)
  refine ⟨MulOpposite.op r,?_⟩
  change bimoduleTargetCornerHom N 1*MulOpposite.op r = MulOpposite.op r
  apply MulOpposite.unop_injective
  apply bimodule_triangular_ext N
  · change (0 : N.LeftRing)*0 = 0
    simp
  · change p.2.unop*1 = p.2.unop
    simp
  · change (0 : N.LeftRing) • (0 : N.Space)+(1 : N.RightRingᵐᵒᵖ) • p.1 = p.1
    simp

def bimoduleTargetRegularEquiv (N : DivisionBimodule.{u}) :
    letI := cornerFixedModule (bimoduleTargetCornerHom N) (BimoduleTriangularRing N)ᵐᵒᵖ
    (N.Space × N.RightRingᵐᵒᵖ) ≃ₗ[N.RightRingᵐᵒᵖ]
      cornerFixedGroup (bimoduleTargetCornerHom N) (BimoduleTriangularRing N)ᵐᵒᵖ := by
  letI := cornerFixedModule (bimoduleTargetCornerHom N) (BimoduleTriangularRing N)ᵐᵒᵖ
  exact {
    toFun := bimoduleTargetRegularElement N
    invFun x := (bimoduleCrossHom N (x : (BimoduleTriangularRing N)ᵐᵒᵖ).unop,
      MulOpposite.op (bimoduleTargetHom N (x : (BimoduleTriangularRing N)ᵐᵒᵖ).unop))
    left_inv _ := rfl
    right_inv x := by
      have hx : bimoduleTargetCornerHom N 1*(x : (BimoduleTriangularRing N)ᵐᵒᵖ) = x := x.property
      have hu := congrArg MulOpposite.unop hx
      apply Subtype.ext
      apply MulOpposite.unop_injective
      apply bimodule_triangular_ext N
      · change (0 : N.LeftRing) = bimoduleSourceHom N (x : (BimoduleTriangularRing N)ᵐᵒᵖ).unop
        have hs := congrArg (bimoduleSourceHom N) hu
        change bimoduleSourceHom N (x : (BimoduleTriangularRing N)ᵐᵒᵖ).unop*0 =
          bimoduleSourceHom N (x : (BimoduleTriangularRing N)ᵐᵒᵖ).unop at hs
        simpa using hs
      · rfl
      · rfl
    map_add' p q := by
      apply Subtype.ext
      apply MulOpposite.unop_injective
      change (((0,((p+q).2).unop),(p+q).1) : BimoduleTriangularRing N) =
        ((0,p.2.unop),p.1)+((0,q.2.unop),q.1)
      apply Prod.ext
      · apply Prod.ext
        · change (0 : N.LeftRing) = 0+0
          simp
        · rfl
      · rfl
    map_smul' a p := by
      apply Subtype.ext
      apply MulOpposite.unop_injective
      apply bimodule_triangular_ext N
      · change (0 : N.LeftRing) = 0*0
        simp
      · rfl
      · change a • p.1 = (0 : N.LeftRing) • (0 : N.Space)+a • p.1
        simp }

theorem bimodule_source_regular_finite (N : DivisionBimodule.{u}) :
    letI := cornerFixedModule (bimoduleSourceCornerHom N) (BimoduleTriangularRing N)ᵐᵒᵖ
    FiniteDimensional N.LeftRingᵐᵒᵖ
      (cornerFixedGroup (bimoduleSourceCornerHom N) (BimoduleTriangularRing N)ᵐᵒᵖ) := by
  letI := cornerFixedModule (bimoduleSourceCornerHom N) (BimoduleTriangularRing N)ᵐᵒᵖ
  exact FiniteDimensional.of_injective (bimoduleSourceRegularEquiv N).symm.toLinearMap
    (bimoduleSourceRegularEquiv N).symm.injective

theorem bimodule_target_regular_finite (N : DivisionBimodule.{u})
    [FiniteDimensional N.RightRingᵐᵒᵖ N.Space] :
    letI := cornerFixedModule (bimoduleTargetCornerHom N) (BimoduleTriangularRing N)ᵐᵒᵖ
    FiniteDimensional N.RightRingᵐᵒᵖ
      (cornerFixedGroup (bimoduleTargetCornerHom N) (BimoduleTriangularRing N)ᵐᵒᵖ) := by
  letI := cornerFixedModule (bimoduleTargetCornerHom N) (BimoduleTriangularRing N)ᵐᵒᵖ
  exact FiniteDimensional.of_injective (bimoduleTargetRegularEquiv N).symm.toLinearMap
    (bimoduleTargetRegularEquiv N).symm.injective

end

end QuantumFlags

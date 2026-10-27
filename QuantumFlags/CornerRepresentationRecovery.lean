import QuantumFlags.CornerHomEquivalence

namespace QuantumFlags

noncomputable section

variable {D : Type*} [DivisionRing D]

def sourceCornerFromArrowEquiv (H : Subfield D) (X : Type*) (Y : Type*)
    [AddCommGroup X] [Module Hᵐᵒᵖ X] [AddCommGroup Y] [Module Dᵐᵒᵖ Y]
    (θ : letI := restrictedRightModule H Y; X →ₗ[Hᵐᵒᵖ] Y) :
    letI := triangularModuleFromArrow H X Y θ
    SourceCorner H (X × Y) ≃ₗ[Hᵐᵒᵖ] X := by
  letI := triangularModuleFromArrow H X Y θ
  exact {
    toFun p := (p : X × Y).1
    invFun x := ⟨(x,0),by
      apply Prod.ext
      · change (1 : Hᵐᵒᵖ) • x = x
        exact one_smul _ _
      · change MulOpposite.op (0 : D) • θ x+MulOpposite.op (0 : D) • (0 : Y) = 0
        simp⟩
    left_inv p := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · have h := congrArg Prod.snd p.property
        change MulOpposite.op (0 : D) • θ (p : X × Y).1+
          MulOpposite.op (0 : D) • (p : X × Y).2 = (p : X × Y).2 at h
        simpa using h
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

def targetCornerFromArrowEquiv (H : Subfield D) (X : Type*) (Y : Type*)
    [AddCommGroup X] [Module Hᵐᵒᵖ X] [AddCommGroup Y] [Module Dᵐᵒᵖ Y]
    (θ : letI := restrictedRightModule H Y; X →ₗ[Hᵐᵒᵖ] Y) :
    letI := triangularModuleFromArrow H X Y θ
    TargetCorner H (X × Y) ≃ₗ[Dᵐᵒᵖ] Y := by
  letI := triangularModuleFromArrow H X Y θ
  exact {
    toFun p := (p : X × Y).2
    invFun y := ⟨(0,y),by
      apply Prod.ext
      · change (0 : Hᵐᵒᵖ) • (0 : X) = 0
        exact zero_smul _ _
      · change MulOpposite.op (0 : D) • θ 0+(1 : Dᵐᵒᵖ) • y = y
        simp⟩
    left_inv p := by
      apply Subtype.ext
      apply Prod.ext
      · have h := congrArg Prod.fst p.property
        change (0 : Hᵐᵒᵖ) • (p : X × Y).1 = (p : X × Y).1 at h
        simpa using h
      · rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' a p := by
      change MulOpposite.op (0 : D) • θ (p : X × Y).1+a • (p : X × Y).2 =
        a • (p : X × Y).2
      simp }

theorem cornerArrow_recovery (H : Subfield D) (X : Type*) (Y : Type*)
    [AddCommGroup X] [Module Hᵐᵒᵖ X] [AddCommGroup Y] [Module Dᵐᵒᵖ Y]
    (θ : letI := restrictedRightModule H Y; X →ₗ[Hᵐᵒᵖ] Y) :
    letI := triangularModuleFromArrow H X Y θ
    ∀ p : SourceCorner H (X × Y),
      targetCornerFromArrowEquiv H X Y θ (cornerArrow H (X × Y) p) =
        θ (sourceCornerFromArrowEquiv H X Y θ p) := by
  letI := triangularModuleFromArrow H X Y θ
  intro p
  change MulOpposite.op (1 : D) • θ (p : X × Y).1+
    MulOpposite.op (0 : D) • (p : X × Y).2 = θ (p : X × Y).1
  simp

def homRepresentationRecovery (H : Subfield D) (M : HomRepresentation (ambientBimodule H)) :
    letI := moduleFromHomRepresentation H M
    HomRepresentationMorphism (cornerHomRepresentation H (M.Source × M.Target)) M := by
  letI : Module Hᵐᵒᵖ M.Source := M.sourceModule
  letI : Module Dᵐᵒᵖ M.Target := M.targetModule
  letI := moduleFromHomRepresentation H M
  exact {
    source := (sourceCornerFromArrowEquiv H M.Source M.Target (ambientRepresentationArrow H M)).toLinearMap
    target := (targetCornerFromArrowEquiv H M.Source M.Target (ambientRepresentationArrow H M)).toLinearMap
    commutes p := by
      apply LinearMap.ext
      intro n
      change M.arrow (sourceCornerFromArrowEquiv H M.Source M.Target (ambientRepresentationArrow H M) p) n =
        targetCornerFromArrowEquiv H M.Source M.Target (ambientRepresentationArrow H M)
          (MulOpposite.op n • cornerArrow H (M.Source × M.Target) p)
      rw [(targetCornerFromArrowEquiv H M.Source M.Target (ambientRepresentationArrow H M)).map_smul,
        cornerArrow_recovery]
      let h := M.arrow (sourceCornerFromArrowEquiv H M.Source M.Target (ambientRepresentationArrow H M) p)
      have hn := h.map_smul (MulOpposite.op n) 1
      change h (1*n) = MulOpposite.op n • h 1 at hn
      simpa only [h,one_mul,ambientRepresentationArrow_apply] using hn }

def homRepresentationRecoveryInverse (H : Subfield D) (M : HomRepresentation (ambientBimodule H)) :
    letI := moduleFromHomRepresentation H M
    HomRepresentationMorphism M (cornerHomRepresentation H (M.Source × M.Target)) := by
  letI : Module Hᵐᵒᵖ M.Source := M.sourceModule
  letI : Module Dᵐᵒᵖ M.Target := M.targetModule
  letI := moduleFromHomRepresentation H M
  let ex := sourceCornerFromArrowEquiv H M.Source M.Target (ambientRepresentationArrow H M)
  let ey := targetCornerFromArrowEquiv H M.Source M.Target (ambientRepresentationArrow H M)
  exact {
    source := ex.symm.toLinearMap
    target := ey.symm.toLinearMap
    commutes x := by
      apply LinearMap.ext
      intro n
      apply ey.injective
      change ey (MulOpposite.op n • cornerArrow H (M.Source × M.Target) (ex.symm x)) =
        ey (ey.symm (M.arrow x n))
      rw [ey.map_smul]
      change MulOpposite.op n • ey (cornerArrow H (M.Source × M.Target) (ex.symm x)) = M.arrow x n
      rw [cornerArrow_recovery,LinearEquiv.apply_symm_apply]
      have hn := (M.arrow x).map_smul (MulOpposite.op n) 1
      change M.arrow x (1*n) = MulOpposite.op n • M.arrow x 1 at hn
      simpa only [one_mul,ambientRepresentationArrow_apply] using hn.symm }

theorem homRepresentationRecovery_left_inverse (H : Subfield D)
    (M : HomRepresentation (ambientBimodule H)) :
    letI := moduleFromHomRepresentation H M
    HomRepresentationMorphism.compose (homRepresentationRecovery H M)
      (homRepresentationRecoveryInverse H M) = HomRepresentationMorphism.identity M := by
  letI : Module Hᵐᵒᵖ M.Source := M.sourceModule
  letI : Module Dᵐᵒᵖ M.Target := M.targetModule
  letI := moduleFromHomRepresentation H M
  apply HomRepresentationMorphism.ext <;> apply LinearMap.ext <;> intro x
  · exact (sourceCornerFromArrowEquiv H M.Source M.Target (ambientRepresentationArrow H M)).apply_symm_apply x
  · exact (targetCornerFromArrowEquiv H M.Source M.Target (ambientRepresentationArrow H M)).apply_symm_apply x

theorem homRepresentationRecovery_right_inverse (H : Subfield D)
    (M : HomRepresentation (ambientBimodule H)) :
    letI := moduleFromHomRepresentation H M
    HomRepresentationMorphism.compose (homRepresentationRecoveryInverse H M)
      (homRepresentationRecovery H M) =
      HomRepresentationMorphism.identity (cornerHomRepresentation H (M.Source × M.Target)) := by
  letI : Module Hᵐᵒᵖ M.Source := M.sourceModule
  letI : Module Dᵐᵒᵖ M.Target := M.targetModule
  letI := moduleFromHomRepresentation H M
  apply HomRepresentationMorphism.ext <;> apply LinearMap.ext <;> intro x
  · exact (sourceCornerFromArrowEquiv H M.Source M.Target (ambientRepresentationArrow H M)).symm_apply_apply x
  · exact (targetCornerFromArrowEquiv H M.Source M.Target (ambientRepresentationArrow H M)).symm_apply_apply x

end

end QuantumFlags

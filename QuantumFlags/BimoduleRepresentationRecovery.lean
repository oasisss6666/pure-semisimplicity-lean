import QuantumFlags.BimoduleRepresentationMaps

namespace QuantumFlags
noncomputable section
universe u
variable (N : DivisionBimodule.{u})

def bimoduleSourceRecoveryEquiv (M : HomRepresentation N) :
    letI := bimoduleModuleFromHomRepresentation N M
    BimoduleSourceCorner N (M.Source × M.Target) ≃ₗ[N.LeftRingᵐᵒᵖ] M.Source := by
  letI := bimoduleModuleFromHomRepresentation N M
  exact {
    toFun p := (p : M.Source × M.Target).1
    invFun x := ⟨(x,0), by
      apply Prod.ext
      · change (1 : N.LeftRingᵐᵒᵖ) • x = x
        exact one_smul _ _
      · change M.arrow x 0 + (0 : N.RightRingᵐᵒᵖ) • (0 : M.Target) = 0
        simp⟩
    left_inv p := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · have h := congrArg Prod.snd p.property
        change M.arrow (p : M.Source × M.Target).1 0 +
          (0 : N.RightRingᵐᵒᵖ) • (p : M.Source × M.Target).2 =
            (p : M.Source × M.Target).2 at h
        simpa using h
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

def bimoduleTargetRecoveryEquiv (M : HomRepresentation N) :
    letI := bimoduleModuleFromHomRepresentation N M
    BimoduleTargetCorner N (M.Source × M.Target) ≃ₗ[N.RightRingᵐᵒᵖ] M.Target := by
  letI := bimoduleModuleFromHomRepresentation N M
  exact {
    toFun p := (p : M.Source × M.Target).2
    invFun y := ⟨(0,y), by
      apply Prod.ext
      · change (0 : N.LeftRingᵐᵒᵖ) • (0 : M.Source) = 0
        exact zero_smul _ _
      · change M.arrow 0 0 + (1 : N.RightRingᵐᵒᵖ) • y = y
        simp⟩
    left_inv p := by
      apply Subtype.ext
      apply Prod.ext
      · have h := congrArg Prod.fst p.property
        change (0 : N.LeftRingᵐᵒᵖ) • (p : M.Source × M.Target).1 =
          (p : M.Source × M.Target).1 at h
        simpa using h
      · rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' a p := by
      change M.arrow (p : M.Source × M.Target).1 0 + a • (p : M.Source × M.Target).2 =
        a • (p : M.Source × M.Target).2
      simp }

def bimoduleHomRepresentationRecovery (M : HomRepresentation N) :
    letI := bimoduleModuleFromHomRepresentation N M
    HomRepresentationMorphism (bimoduleCornerHomRepresentation N (M.Source × M.Target)) M := by
  letI := bimoduleModuleFromHomRepresentation N M
  exact {
    source := (bimoduleSourceRecoveryEquiv N M).toLinearMap
    target := (bimoduleTargetRecoveryEquiv N M).toLinearMap
    commutes x := by
      apply LinearMap.ext
      intro n
      change M.arrow (x : M.Source × M.Target).1 n =
        M.arrow (x : M.Source × M.Target).1 n +
          (0 : N.RightRingᵐᵒᵖ) • (x : M.Source × M.Target).2
      simp }

def bimoduleHomRepresentationRecoveryInverse (M : HomRepresentation N) :
    letI := bimoduleModuleFromHomRepresentation N M
    HomRepresentationMorphism M (bimoduleCornerHomRepresentation N (M.Source × M.Target)) := by
  letI := bimoduleModuleFromHomRepresentation N M
  let ex := bimoduleSourceRecoveryEquiv N M
  let ey := bimoduleTargetRecoveryEquiv N M
  exact {
    source := ex.symm.toLinearMap
    target := ey.symm.toLinearMap
    commutes x := by
      apply LinearMap.ext
      intro n
      apply ey.injective
      change M.arrow x n + (0 : N.RightRingᵐᵒᵖ) • (0 : M.Target) = M.arrow x n
      simp }

theorem bimoduleHomRepresentationRecovery_left_inverse (M : HomRepresentation N) :
    letI := bimoduleModuleFromHomRepresentation N M
    HomRepresentationMorphism.compose (bimoduleHomRepresentationRecovery N M)
      (bimoduleHomRepresentationRecoveryInverse N M) = HomRepresentationMorphism.identity M := by
  letI := bimoduleModuleFromHomRepresentation N M
  apply HomRepresentationMorphism.ext <;> apply LinearMap.ext <;> intro x
  · exact (bimoduleSourceRecoveryEquiv N M).apply_symm_apply x
  · exact (bimoduleTargetRecoveryEquiv N M).apply_symm_apply x

theorem bimoduleHomRepresentationRecovery_right_inverse (M : HomRepresentation N) :
    letI := bimoduleModuleFromHomRepresentation N M
    HomRepresentationMorphism.compose (bimoduleHomRepresentationRecoveryInverse N M)
      (bimoduleHomRepresentationRecovery N M) =
        HomRepresentationMorphism.identity (bimoduleCornerHomRepresentation N (M.Source × M.Target)) := by
  letI := bimoduleModuleFromHomRepresentation N M
  apply HomRepresentationMorphism.ext <;> apply LinearMap.ext <;> intro x
  · exact (bimoduleSourceRecoveryEquiv N M).symm_apply_apply x
  · exact (bimoduleTargetRecoveryEquiv N M).symm_apply_apply x

theorem bimoduleHomRepresentationRecovery_natural {M P : HomRepresentation N}
    (f : HomRepresentationMorphism M P) :
    letI := bimoduleModuleFromHomRepresentation N M
    letI := bimoduleModuleFromHomRepresentation N P
    HomRepresentationMorphism.compose (bimoduleHomRepresentationRecovery N P)
      (bimoduleCornerHomRepresentationMap N (bimoduleHomRepresentationModuleMap N f)) =
        HomRepresentationMorphism.compose f (bimoduleHomRepresentationRecovery N M) := by
  letI := bimoduleModuleFromHomRepresentation N M
  letI := bimoduleModuleFromHomRepresentation N P
  apply HomRepresentationMorphism.ext <;> apply LinearMap.ext <;> intro x <;> rfl

end
end QuantumFlags

import QuantumFlags.TensorReflectionRecoverIso
import QuantumFlags.PreinjectiveReflection
import QuantumFlags.ReflectionDefectStep

namespace QuantumFlags
noncomputable section
open CategoryTheory
universe u v
variable {N : DivisionBimodule.{u}}

theorem positiveDefect_classification_by_target (C : RightReflectionChain N) (b : ℕ) :
    ∀ (r : ℕ) (M : TensorRepresentation.{u,max u v,max u v} (iteratedRightDual N r))
      [FiniteDimensional (iteratedRightDual N r).LeftRingᵐᵒᵖ M.Source]
      [FiniteDimensional (iteratedRightDual N r).RightRingᵐᵒᵖ M.Target],
    Module.finrank (iteratedRightDual N r).RightRingᵐᵒᵖ M.Target = b →
    Indecomposable M →
    Module.finrank (iteratedRightDual N r).RightRingᵐᵒᵖ M.Target <
      Module.finrank (iteratedRightDual N r).LeftRingᵐᵒᵖ M.Source →
    Nonempty (M ≅ (preinjectiveFamily.{u,v} C b r).obj) := by
  induction b using Nat.strong_induction_on with
  | h b ih =>
    intro r M _ _ hb hM hdef
    let A := iteratedRightDual N r
    change Module.finrank A.RightRingᵐᵒᵖ M.Target = b at hb
    change Module.finrank A.RightRingᵐᵒᵖ M.Target < Module.finrank A.LeftRingᵐᵒᵖ M.Source at hdef
    letI : FiniteDimensional A.RightRingᵐᵒᵖ A.Space := C.finite r
    letI := dualRightModule A
    letI : FiniteDimensional A.LeftRingᵐᵒᵖ (RightDualSpace A) := C.finite (r+1)
    by_cases hS : Nonempty (M ≅ tensorSimpleSource.{u,v} A)
    · obtain ⟨e⟩ := hS
      have hz := tensorIso_target_finrank e
      rw [simpleSource_target_finrank] at hz
      have hzero : b = 0 := hb.symm.trans hz
      rw [hzero]
      exact ⟨e⟩
    · have hβ := indecomposable_tensorAdjoint_injective A M hM hS
      let J : InjectiveTensorObjects.{u,v} A := ⟨M,hβ⟩
      let F := reflectionForward A (tensorRepresentationToHom M)
      letI : Module (iteratedRightDual N (r+1)).LeftRingᵐᵒᵖ F.Source := F.sourceModule
      letI : Module (iteratedRightDual N (r+1)).RightRingᵐᵒᵖ F.Target := F.targetModule
      letI : FiniteDimensional (iteratedRightDual N (r+1)).LeftRingᵐᵒᵖ F.Source :=
        reflectionForwardSourceFinite A (tensorRepresentationToHom M)
      letI : FiniteDimensional (iteratedRightDual N (r+1)).RightRingᵐᵒᵖ F.Target :=
        reflectionForwardTargetFinite A (tensorRepresentationToHom M)
      have hF : Indecomposable F := (tensorReflection_ambient_indecomposable_iff A J).mpr hM
      have hstep := tensorReflection_positive_defect_step A J (C.double r) hdef
      change Module.finrank A.LeftRingᵐᵒᵖ F.Target < Module.finrank A.RightRingᵐᵒᵖ M.Target ∧
        Module.finrank A.RightRingᵐᵒᵖ F.Source - Module.finrank A.LeftRingᵐᵒᵖ F.Target =
          Module.finrank A.LeftRingᵐᵒᵖ M.Source - Module.finrank A.RightRingᵐᵒᵖ M.Target at hstep
      let j := Module.finrank A.LeftRingᵐᵒᵖ F.Target
      have hj : j < b := by dsimp [j]; omega
      have hpos : Module.finrank A.LeftRingᵐᵒᵖ F.Target <
          Module.finrank A.RightRingᵐᵒᵖ F.Source := by omega
      obtain ⟨e⟩ := ih j hj (r+1) F rfl hF hpos
      have hdim := tensorIso_source_finrank e
      change Module.finrank (iteratedRightDual N (r+1)).LeftRingᵐᵒᵖ F.Source =
        Module.finrank (iteratedRightDual N (r+1)).LeftRingᵐᵒᵖ
          (preinjectiveFamily C j (r+1)).obj.Source at hdim
      rw [(preinjectiveFamily C j (r+1)).source_finrank] at hdim
      change Module.finrank A.RightRingᵐᵒᵖ M.Target = j+1 at hdim
      have hbj : b = j+1 := hb.symm.trans hdim
      let L : SurjectiveDualTensorObjects.{u,v} A :=
        ⟨(preinjectiveFamily C j (r+1)).obj, (preinjectiveFamily C j (r+1)).arrow_surjective⟩
      have he := tensorReflectionRecoverIso A J L e
      rw [hbj]
      exact ⟨he⟩

theorem positiveDefect_classification (C : RightReflectionChain N) (r : ℕ)
    (M : TensorRepresentation.{u,max u v,max u v} (iteratedRightDual N r))
    [FiniteDimensional (iteratedRightDual N r).LeftRingᵐᵒᵖ M.Source]
    [FiniteDimensional (iteratedRightDual N r).RightRingᵐᵒᵖ M.Target]
    (hM : Indecomposable M)
    (hdef : Module.finrank (iteratedRightDual N r).RightRingᵐᵒᵖ M.Target <
      Module.finrank (iteratedRightDual N r).LeftRingᵐᵒᵖ M.Source) :
    Nonempty (M ≅ (preinjectiveFamily.{u,v} C
      (Module.finrank (iteratedRightDual N r).RightRingᵐᵒᵖ M.Target) r).obj) :=
  positiveDefect_classification_by_target C _ r M rfl hM hdef

end
end QuantumFlags

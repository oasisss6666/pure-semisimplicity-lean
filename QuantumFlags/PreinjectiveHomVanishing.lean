import QuantumFlags.PositiveDefectClassification
import QuantumFlags.SimpleHomVanishing

/-!
# Hom vanishing out of the preinjective family

Manuscript `prop:class`, second paragraph of the proof (source line 222).  For `k < l` the
morphisms `I_k → I_l` and `I_k → P` vanish: applying the reflections `Φ_{k-1} ⋯ Φ_0` turns `I_k`
into the simple source `S_k`, while `I_l` and `P` become indecomposable objects that are not
simple sources, so the boundary vanishing and full faithfulness apply.

The induction is carried out at every layer `r` for an arbitrary finite-dimensional
indecomposable target object `Y` with dimension vector `(a,b)` satisfying `b ≤ a` and
`k (a - b) < b`.  These two conditions are exactly what survives `k` reflections without
reaching a simple source: one reflection sends `(a,b)` to `(b, 2b-a)`, preserving the defect
`a - b` and lowering `b` by it.  The objects `I_l` (`l > k`, defect `1`) and `P` (dimension
vector `(1,1)`, defect `0`) satisfy them at layer `0`.
-/

namespace QuantumFlags
noncomputable section
open CategoryTheory
universe u v
variable {N : DivisionBimodule.{u}}

theorem preinjectiveFamily_hom_subsingleton (C : RightReflectionChain N) (k : ℕ) :
    ∀ (r : ℕ) (Y : TensorRepresentation.{u,max u v,max u v} (iteratedRightDual N r))
      [FiniteDimensional (iteratedRightDual N r).LeftRingᵐᵒᵖ Y.Source]
      [FiniteDimensional (iteratedRightDual N r).RightRingᵐᵒᵖ Y.Target],
    Indecomposable Y →
    Module.finrank (iteratedRightDual N r).RightRingᵐᵒᵖ Y.Target ≤
      Module.finrank (iteratedRightDual N r).LeftRingᵐᵒᵖ Y.Source →
    k * (Module.finrank (iteratedRightDual N r).LeftRingᵐᵒᵖ Y.Source -
        Module.finrank (iteratedRightDual N r).RightRingᵐᵒᵖ Y.Target) <
      Module.finrank (iteratedRightDual N r).RightRingᵐᵒᵖ Y.Target →
    Subsingleton ((preinjectiveFamily.{u,v} C k r).obj ⟶ Y) := by
  induction k with
  | zero =>
    intro r Y _ _ hY _ hlt
    let A := iteratedRightDual N r
    have hb : 0 < Module.finrank A.RightRingᵐᵒᵖ Y.Target := by simpa using hlt
    have hβ := indecomposable_tensorAdjoint_injective A Y hY (positiveTarget_not_simpleSource hb)
    exact ⟨fun f g => (tensorHomFromSimpleSource_eq_zero A Y hβ f).trans
      (tensorHomFromSimpleSource_eq_zero A Y hβ g).symm⟩
  | succ k ih =>
    intro r Y _ _ hY hle hlt
    let A := iteratedRightDual N r
    letI : FiniteDimensional A.RightRingᵐᵒᵖ A.Space := C.finite r
    letI := dualRightModule A
    letI : FiniteDimensional A.LeftRingᵐᵒᵖ (RightDualSpace A) := C.finite (r+1)
    change Module.finrank A.RightRingᵐᵒᵖ Y.Target ≤ Module.finrank A.LeftRingᵐᵒᵖ Y.Source at hle
    change (k+1) * (Module.finrank A.LeftRingᵐᵒᵖ Y.Source -
        Module.finrank A.RightRingᵐᵒᵖ Y.Target) < Module.finrank A.RightRingᵐᵒᵖ Y.Target at hlt
    have hb : 0 < Module.finrank A.RightRingᵐᵒᵖ Y.Target :=
      Nat.lt_of_le_of_lt (Nat.zero_le _) hlt
    have hβY := indecomposable_tensorAdjoint_injective A Y hY (positiveTarget_not_simpleSource hb)
    let P := preinjectiveFamily.{u,v} C (k+1) r
    have hPt : 0 < Module.finrank A.RightRingᵐᵒᵖ P.obj.Target := by
      rw [P.target_finrank]; omega
    have hβP := indecomposable_tensorAdjoint_injective A P.obj
      (preinjectiveFamily_indecomposable C (k+1) r) (positiveTarget_not_simpleSource hPt)
    let JP : InjectiveTensorObjects.{u,v} A := ⟨P.obj, hβP⟩
    let JY : InjectiveTensorObjects.{u,v} A := ⟨Y, hβY⟩
    let E := tensorReflectionEquivalence.{u,v} A
    let F := reflectionForward A (tensorRepresentationToHom Y)
    letI : Module (iteratedRightDual N (r+1)).LeftRingᵐᵒᵖ F.Source := F.sourceModule
    letI : Module (iteratedRightDual N (r+1)).RightRingᵐᵒᵖ F.Target := F.targetModule
    letI : FiniteDimensional (iteratedRightDual N (r+1)).LeftRingᵐᵒᵖ F.Source :=
      reflectionForwardSourceFinite A (tensorRepresentationToHom Y)
    letI : FiniteDimensional (iteratedRightDual N (r+1)).RightRingᵐᵒᵖ F.Target :=
      reflectionForwardTargetFinite A (tensorRepresentationToHom Y)
    have hF : Indecomposable F := (tensorReflection_ambient_indecomposable_iff A JY).mpr hY
    have hD : Module.finrank A.LeftRingᵐᵒᵖ (RightDualSpace A) = 2 := C.double r
    have hd := tensorReflection_dimension_vector A JY
    rw [hD] at hd
    have hs : Module.finrank A.RightRingᵐᵒᵖ F.Source = Module.finrank A.RightRingᵐᵒᵖ Y.Target :=
      congrArg Prod.fst hd
    have ht : Module.finrank A.LeftRingᵐᵒᵖ F.Target =
        2 * Module.finrank A.RightRingᵐᵒᵖ Y.Target - Module.finrank A.LeftRingᵐᵒᵖ Y.Source :=
      congrArg Prod.snd hd
    have hu := tensorRepresentation_source_finrank_le A Y hβY
    rw [hD] at hu
    have hle' : Module.finrank (iteratedRightDual N (r+1)).RightRingᵐᵒᵖ F.Target ≤
        Module.finrank (iteratedRightDual N (r+1)).LeftRingᵐᵒᵖ F.Source := by
      change Module.finrank A.LeftRingᵐᵒᵖ F.Target ≤ Module.finrank A.RightRingᵐᵒᵖ F.Source
      rw [hs, ht]; omega
    have hlt' : k * (Module.finrank (iteratedRightDual N (r+1)).LeftRingᵐᵒᵖ F.Source -
          Module.finrank (iteratedRightDual N (r+1)).RightRingᵐᵒᵖ F.Target) <
        Module.finrank (iteratedRightDual N (r+1)).RightRingᵐᵒᵖ F.Target := by
      change k * (Module.finrank A.RightRingᵐᵒᵖ F.Source -
          Module.finrank A.LeftRingᵐᵒᵖ F.Target) < Module.finrank A.LeftRingᵐᵒᵖ F.Target
      rw [hs, ht]
      have hdef : Module.finrank A.RightRingᵐᵒᵖ Y.Target -
          (2 * Module.finrank A.RightRingᵐᵒᵖ Y.Target - Module.finrank A.LeftRingᵐᵒᵖ Y.Source) =
          Module.finrank A.LeftRingᵐᵒᵖ Y.Source - Module.finrank A.RightRingᵐᵒᵖ Y.Target := by
        omega
      rw [hdef]
      rw [Nat.succ_mul] at hlt
      omega
    have hsub : Subsingleton ((preinjectiveFamily.{u,v} C k (r+1)).obj ⟶ F) :=
      ih (r+1) F hF hle' hlt'
    have hrefl : Subsingleton (reflectionForward A (tensorRepresentationToHom P.obj) ⟶ F) :=
      @Equiv.subsingleton _ _ (Iso.homCongr (preinjectiveFamilyReflectionIso C k r) (Iso.refl F)) hsub
    exact @Equiv.subsingleton (JP ⟶ JY) (E.functor.obj JP ⟶ E.functor.obj JY)
      E.fullyFaithfulFunctor.homEquiv hrefl

end
end QuantumFlags

import QuantumFlags.RepresentationKernel

namespace QuantumFlags
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
variable {N : DivisionBimodule.{u}} {S M : HomRepresentation.{u,max u v,max u v} N}

def homRepresentationSplitBicone (i : S ⟶ M) (p : M ⟶ S) (hpi : i ≫ p = 𝟙 S) :
    BinaryBicone S (homRepresentationKernel p) where
  pt := M
  fst := p
  snd := homRepresentationKernelProjection i p hpi
  inl := i
  inr := homRepresentationKernelInclusion p
  inl_fst := hpi
  inl_snd := by
    apply HomRepresentationMorphism.ext
    · exact splitKernelProjection_comp_section i.source p.source
        (congrArg HomRepresentationMorphism.source hpi)
    · exact splitKernelProjection_comp_section i.target p.target
        (congrArg HomRepresentationMorphism.target hpi)
  inr_fst := by
    apply HomRepresentationMorphism.ext <;> apply LinearMap.ext <;> intro x
    · exact x.property
    · exact x.property
  inr_snd := by
    apply HomRepresentationMorphism.ext
    · exact splitKernelProjection_comp_inclusion i.source p.source
        (congrArg HomRepresentationMorphism.source hpi)
    · exact splitKernelProjection_comp_inclusion i.target p.target
        (congrArg HomRepresentationMorphism.target hpi)

theorem homRepresentationSplitBicone_total (i : S ⟶ M) (p : M ⟶ S) (hpi : i ≫ p = 𝟙 S) :
    (homRepresentationSplitBicone i p hpi).fst ≫ (homRepresentationSplitBicone i p hpi).inl +
      (homRepresentationSplitBicone i p hpi).snd ≫ (homRepresentationSplitBicone i p hpi).inr =
        𝟙 M := by
  apply HomRepresentationMorphism.ext
  · exact splitKernelProjection_total i.source p.source
      (congrArg HomRepresentationMorphism.source hpi)
  · exact splitKernelProjection_total i.target p.target
      (congrArg HomRepresentationMorphism.target hpi)

def homRepresentationSplitIso (i : S ⟶ M) (p : M ⟶ S) (hpi : i ≫ p = 𝟙 S) :
    M ≅ S ⊞ homRepresentationKernel p :=
  biprod.uniqueUpToIso _ _ (isBinaryBilimitOfTotal (homRepresentationSplitBicone i p hpi)
    (homRepresentationSplitBicone_total i p hpi))

theorem indecomposable_retract_isomorphism (hM : Indecomposable M) (hS : ¬ IsZero S)
    (i : S ⟶ M) (p : M ⟶ S) (hpi : i ≫ p = 𝟙 S) : Nonempty (M ≅ S) := by
  rcases hM.2 S (homRepresentationKernel p) (homRepresentationSplitIso i p hpi) with hzero | hker
  · exact False.elim (hS hzero)
  · have hq : homRepresentationKernelProjection i p hpi = 0 := hker.eq_of_tgt _ _
    have ht := homRepresentationSplitBicone_total i p hpi
    change p ≫ i + homRepresentationKernelProjection i p hpi ≫
      homRepresentationKernelInclusion p = 𝟙 M at ht
    rw [hq, zero_comp, add_zero] at ht
    exact ⟨{ hom := p, inv := i, hom_inv_id := ht, inv_hom_id := hpi }⟩

end
end QuantumFlags

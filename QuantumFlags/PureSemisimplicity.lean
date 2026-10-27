import QuantumFlags.ClassificationList
import QuantumFlags.DecompositionLemma
import QuantumFlags.ModuleIndecomposableCriteria
import QuantumFlags.FiniteRightModuleClassification
import QuantumFlags.PureSemisimpleDefs

/-!
# Right pure semisimplicity from the dimension sequence

Manuscript `thm:pss` (source lines 225-231), together with the module form of `prop:class`.
For a division bimodule `N` with right dimension sequence `(1,2,2,...)`, the modules of the
ordered list `E₁ < I₁ < I₂ < ⋯ < P < E₂`, transported along the actual equivalence between
representations and right modules of the triangular ring `R_N`, form a complete irredundant list
of finitely generated indecomposable right `R_N`-modules with division endomorphism rings and
ordered Hom vanishing.  The decomposition lemma then writes every right `R_N`-module as a direct
sum of copies of these modules, so `R_N` is right pure semisimple.

Right `Λ`-modules are modules over `Λᵐᵒᵖ`.  Pure semisimplicity is stated for the modules in a
fixed universe `w`; for `N : DivisionBimodule.{u}` the theorem covers every universe `max u v`,
hence every universe when `u = 0`, as for the actual counterexample.
-/

namespace QuantumFlags
noncomputable section
open CategoryTheory DirectSum
universe u v w

variable {N : DivisionBimodule.{u}}

/-- The right `R_N`-module of the classification list with the given index. -/
abbrev classModule (C : RightReflectionChain N) (i : ClassIndex) :
    ModuleCat.{max u v} (BimoduleTriangularRing N)ᵐᵒᵖ :=
  (bimoduleTensorRepresentationEquivalence.{u,v} N).functor.obj (classObject.{u,v} C i)

section ClassModules

variable (C : RightReflectionChain N) (hN : Module.finrank N.RightRingᵐᵒᵖ N.Space = 1)
include C hN

theorem classModule_finite (i : ClassIndex) :
    Module.Finite (BimoduleTriangularRing N)ᵐᵒᵖ (classModule.{u,v} C i) := by
  letI : FiniteDimensional N.RightRingᵐᵒᵖ N.Space := C.finite 0
  letI := classObject_source_finite.{u,v} C hN i
  letI := classObject_target_finite.{u,v} C hN i
  exact bimoduleTensorRepresentation_finite N (classObject C i)

theorem classModule_finitelyPresented (i : ClassIndex) :
    Module.FinitePresentation (BimoduleTriangularRing N)ᵐᵒᵖ (classModule.{u,v} C i) := by
  letI : FiniteDimensional N.RightRingᵐᵒᵖ N.Space := C.finite 0
  letI := classModule_finite.{u,v} C hN i
  exact bimodule_finite_presentation N (classModule C i)

omit hN in
/-- Every nonzero endomorphism of a listed module is invertible. -/
theorem classModule_endRing_isUnit (i : ClassIndex)
    (f : Module.End (BimoduleTriangularRing N)ᵐᵒᵖ (classModule.{u,v} C i)) (hf : f ≠ 0) :
    IsUnit f := by
  obtain ⟨K, _, ⟨φ⟩⟩ := classObject_endRing_division.{u,v} C i
  let θ : Module.End (BimoduleTriangularRing N)ᵐᵒᵖ (classModule.{u,v} C i) ≃+* K :=
    (ModuleCat.endRingEquiv (classModule.{u,v} C i)).symm.trans
      ((bimoduleTensorRepresentationEndRingEquiv N (classObject C i)).symm.trans φ)
  have hθ : θ f ≠ 0 := by
    intro h
    apply hf
    rw [← map_zero θ] at h
    exact θ.injective h
  exact (MulEquiv.isUnit_map θ.toMulEquiv).mp (Ne.isUnit hθ)

omit hN in
theorem classModule_nontrivial (i : ClassIndex) : Nontrivial (classModule.{u,v} C i) := by
  have h := (bimoduleTensorRepresentation_indecomposable_iff N (classObject C i)).mpr
    (classObject_indecomposable C i)
  by_contra hs
  rw [not_nontrivial_iff_subsingleton] at hs
  exact h.1 (ModuleCat.isZero_of_subsingleton _)

omit hN in
theorem classModule_indecomposable (i : ClassIndex) :
    ModuleIndecomposable (BimoduleTriangularRing N)ᵐᵒᵖ (classModule.{u,v} C i) := by
  haveI := classModule_nontrivial.{u,v} C i
  exact moduleIndecomposable_of_isUnit (classModule_endRing_isUnit C i)

/-- Manuscript `prop:class`, completeness for right modules: every finitely generated
indecomposable right `R_N`-module is isomorphic to a listed module. -/
theorem classModule_complete (F : Type (max u v)) [AddCommGroup F]
    [Module (BimoduleTriangularRing N)ᵐᵒᵖ F] [hfin : Module.Finite (BimoduleTriangularRing N)ᵐᵒᵖ F]
    (hF : ModuleIndecomposable (BimoduleTriangularRing N)ᵐᵒᵖ F) :
    ∃ i : ClassIndex, Nonempty (F ≃ₗ[(BimoduleTriangularRing N)ᵐᵒᵖ] classModule.{u,v} C i) := by
  let Fc := ModuleCat.of (BimoduleTriangularRing N)ᵐᵒᵖ F
  have hFc : Indecomposable Fc := indecomposable_of_moduleIndecomposable Fc hF
  haveI : Module.Finite (BimoduleTriangularRing N)ᵐᵒᵖ Fc := hfin
  rcases finiteRightModule_indecomposable_classification.{u,v} C hN Fc hFc with
    h | h | h | ⟨k, _, h⟩
  · obtain ⟨e⟩ := h
    exact ⟨toLex (Sum.inl 0), ⟨e.toLinearEquiv⟩⟩
  · obtain ⟨e⟩ := h
    exact ⟨toLex (Sum.inr true), ⟨e.toLinearEquiv⟩⟩
  · obtain ⟨e⟩ := h
    exact ⟨toLex (Sum.inr false), ⟨e.toLinearEquiv⟩⟩
  · obtain ⟨e⟩ := h
    exact ⟨toLex (Sum.inl k), ⟨e.toLinearEquiv⟩⟩

/-- Manuscript `prop:class`, irredundancy for right modules. -/
theorem classModule_irredundant {i j : ClassIndex}
    (e : Nonempty (classModule.{u,v} C i ≃ₗ[(BimoduleTriangularRing N)ᵐᵒᵖ] classModule.{u,v} C j)) :
    i = j := by
  obtain ⟨e⟩ := e
  let f : classModule.{u,v} C i ≅ classModule.{u,v} C j := e.toModuleIso
  exact classObject_irredundant C hN
    ⟨(bimoduleTensorRepresentationEquivalence N).fullyFaithfulFunctor.preimageIso f⟩

/-- Manuscript `prop:class`, ordered Hom vanishing for right modules. -/
theorem classModule_hom_eq_zero {i j : ClassIndex} (hij : i < j)
    (f : classModule.{u,v} C i →ₗ[(BimoduleTriangularRing N)ᵐᵒᵖ] classModule.{u,v} C j) :
    f = 0 := by
  haveI : Subsingleton (classModule.{u,v} C i ⟶ classModule.{u,v} C j) :=
    @Equiv.subsingleton _ _ (bimoduleTensorRepresentationEquivalence N).fullyFaithfulFunctor.homEquiv.symm
      (classObject_hom_subsingleton C hN hij)
  have h : ModuleCat.ofHom f = (0 : classModule.{u,v} C i ⟶ classModule.{u,v} C j) :=
    Subsingleton.elim _ _
  have := congrArg ModuleCat.Hom.hom h
  simpa using this

/-- Manuscript `thm:pss`, first assertion: every right `R_N`-module is a direct sum of copies of
the listed modules. -/
theorem triangular_module_decomposition (M : Type (max u v)) [AddCommGroup M]
    [Module (BimoduleTriangularRing N)ᵐᵒᵖ M] :
    ∃ (κ : Type (max u v)) (β : κ → ClassIndex),
      Nonempty (M ≃ₗ[(BimoduleTriangularRing N)ᵐᵒᵖ] ⨁ k, classModule.{u,v} C (β k)) := by
  letI : FiniteDimensional N.RightRingᵐᵒᵖ N.Space := C.finite 0
  haveI := bimodule_triangular_op_artinian N
  exact decomposition_lemma (R := (BimoduleTriangularRing N)ᵐᵒᵖ) (I := ClassIndex)
    (fun i => classModule.{u,v} C i) (classModule_finite C hN) (classModule_indecomposable C)
    (fun F _ _ hfin hF => classModule_complete C hN F hF)
    (fun _ _ e => classModule_irredundant C hN e)
    (classModule_endRing_isUnit C) (fun _ _ hij f => classModule_hom_eq_zero C hN hij f) M

/-- Manuscript `thm:pss`: the triangular ring `R_N` is right pure semisimple. -/
theorem triangular_right_pure_semisimple :
    IsRightPureSemisimple.{u, max u v} (BimoduleTriangularRing N) := by
  intro M _ _
  obtain ⟨κ, β, ⟨e⟩⟩ := triangular_module_decomposition.{u,v} C hN M
  exact ⟨κ, fun k => classModule.{u,v} C (β k), fun _ => inferInstance, fun _ => inferInstance,
    fun k => classModule_finite C hN (β k), ⟨e⟩⟩

/-- Manuscript `prop:class`, last sentence of the first paragraph of the proof: every finitely
generated right `R_N`-module is a finite direct sum of listed modules. -/
theorem finitelyGenerated_triangular_decomposition (F : Type (max u v)) [AddCommGroup F]
    [Module (BimoduleTriangularRing N)ᵐᵒᵖ F] [Module.Finite (BimoduleTriangularRing N)ᵐᵒᵖ F] :
    ∃ (κ : Type) (_ : Fintype κ) (β : κ → ClassIndex),
      Nonempty (F ≃ₗ[(BimoduleTriangularRing N)ᵐᵒᵖ] ((k : κ) → classModule.{u,v} C (β k))) := by
  letI : FiniteDimensional N.RightRingᵐᵒᵖ N.Space := C.finite 0
  haveI := bimodule_triangular_op_artinian N
  exact finite_decomposition (R := (BimoduleTriangularRing N)ᵐᵒᵖ)
    (fun i => classModule.{u,v} C i) (fun F _ _ hfin hF => classModule_complete C hN F hF) F

/-- Manuscript `thm:pss`, last assertion: the modules `I_k`, `k ≥ 1`, are pairwise nonisomorphic
finitely generated indecomposable right `R_N`-modules, so there are infinitely many isomorphism
classes of finitely generated indecomposable right `R_N`-modules. -/
theorem triangular_not_finitelyManyIndecomposables :
    ¬ FinitelyManyIndecomposables.{u, max u v} (BimoduleTriangularRing N)ᵐᵒᵖ := by
  apply not_finitelyManyIndecomposables (fun k => classModule.{u,v} C (toLex (Sum.inl (k+1))))
  · exact fun k => classModule_finite C hN _
  · exact fun k => classModule_indecomposable C _
  · intro k l hkl e
    have := classModule_irredundant C hN e
    simp only [EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq, add_left_inj] at this
    exact hkl this

end ClassModules

end
end QuantumFlags

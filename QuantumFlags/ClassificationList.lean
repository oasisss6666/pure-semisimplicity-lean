import QuantumFlags.FiniteIndecomposableClassification
import QuantumFlags.PreinjectiveHomVanishing

/-!
# The ordered list of finite indecomposables

Manuscript `prop:class` (source lines 212-222) for a division bimodule `N` with right dimension
sequence `(1,2,2,...)`.  The list is indexed by the well-ordered set `ℕ ⊕ₗ Bool`, with

* `inl 0 ↦ E₁`, the simple source, which is the member `I₀` of the preinjective family;
* `inl k ↦ I_k` for `k ≥ 1`;
* `inr false ↦ P`, the canonical projective `(G, F, mult)`;
* `inr true ↦ E₂`, the simple target;

so the order of the index set is the order `E₁ < I₁ < I₂ < ⋯ < P < E₂` of the manuscript.
This file proves that the list is complete and irredundant, that every member has a division
endomorphism ring, and that `Hom(C, C') = 0` whenever `C` precedes `C'`.
-/

namespace QuantumFlags
noncomputable section
open CategoryTheory
universe u v
variable {N : DivisionBimodule.{u}}

/-- Index set of the classification, ordered as `E₁ < I₁ < I₂ < ⋯ < P < E₂`. -/
abbrev ClassIndex := ℕ ⊕ₗ Bool

/-- The order `E₁ < I₁ < I₂ < ⋯ < P < E₂` is a well order. -/
instance classIndexWellFoundedLT : WellFoundedLT ClassIndex :=
  Sum.lex_wf wellFounded_lt wellFounded_lt

/-- The member of the classification list with the given index. -/
def classObject (C : RightReflectionChain N) (i : ClassIndex) :
    TensorRepresentation.{u,max u v,max u v} N :=
  Sum.elim (fun k => preinjectiveRepresentation.{u,v} C k)
    (fun b => cond b (tensorSimpleTarget.{u,v} N) (tensorCanonicalProjective.{u,v} N)) (ofLex i)

theorem classObject_inl (C : RightReflectionChain N) (k : ℕ) :
    classObject.{u,v} C (toLex (Sum.inl k)) = preinjectiveRepresentation.{u,v} C k := rfl

theorem classObject_projective (C : RightReflectionChain N) :
    classObject.{u,v} C (toLex (Sum.inr false)) = tensorCanonicalProjective.{u,v} N := rfl

theorem classObject_target (C : RightReflectionChain N) :
    classObject.{u,v} C (toLex (Sum.inr true)) = tensorSimpleTarget.{u,v} N := rfl

/-- The first member of the list is the simple source `E₁`. -/
theorem classObject_source (C : RightReflectionChain N) :
    classObject.{u,v} C (toLex (Sum.inl 0)) = tensorSimpleSource.{u,v} N := rfl

section Dimensions

variable (C : RightReflectionChain N) (hN : Module.finrank N.RightRingᵐᵒᵖ N.Space = 1)
include hN

theorem classObject_source_finrank_pos_or (i : ClassIndex) :
    (∃ k : ℕ, i = toLex (Sum.inl k) ∧
        Module.finrank N.LeftRingᵐᵒᵖ (classObject.{u,v} C i).Source = k+1 ∧
        Module.finrank N.RightRingᵐᵒᵖ (classObject.{u,v} C i).Target = k) ∨
      (i = toLex (Sum.inr false) ∧
        Module.finrank N.LeftRingᵐᵒᵖ (classObject.{u,v} C i).Source = 1 ∧
        Module.finrank N.RightRingᵐᵒᵖ (classObject.{u,v} C i).Target = 1) ∨
      (i = toLex (Sum.inr true) ∧
        Module.finrank N.LeftRingᵐᵒᵖ (classObject.{u,v} C i).Source = 0 ∧
        Module.finrank N.RightRingᵐᵒᵖ (classObject.{u,v} C i).Target = 1) := by
  induction i using Lex.rec with
  | h i =>
    rcases i with k | b
    · exact Or.inl ⟨k, rfl, (preinjectiveFamily C k 0).source_finrank,
        (preinjectiveFamily C k 0).target_finrank⟩
    · cases b
      · exact Or.inr (Or.inl ⟨rfl, congrArg Prod.fst (canonicalProjective_dimension_vector N hN),
          congrArg Prod.snd (canonicalProjective_dimension_vector N hN)⟩)
      · exact Or.inr (Or.inr ⟨rfl, simpleTarget_source_finrank N, simpleTarget_target_finrank N⟩)

end Dimensions

theorem classObject_source_finite (C : RightReflectionChain N)
    (hN : Module.finrank N.RightRingᵐᵒᵖ N.Space = 1) (i : ClassIndex) :
    FiniteDimensional N.LeftRingᵐᵒᵖ (classObject.{u,v} C i).Source := by
  induction i using Lex.rec with
  | h i =>
    rcases i with k | b
    · exact (preinjectiveFamily C k 0).sourceFinite
    · cases b
      · apply Module.finite_of_finrank_pos
        have h : Module.finrank N.LeftRingᵐᵒᵖ (tensorCanonicalProjective.{u,v} N).Source = 1 :=
          congrArg Prod.fst (canonicalProjective_dimension_vector.{u,v} N hN)
        change 0 < Module.finrank N.LeftRingᵐᵒᵖ (tensorCanonicalProjective.{u,v} N).Source
        rw [h]
        exact Nat.one_pos
      · change FiniteDimensional N.LeftRingᵐᵒᵖ PUnit
        infer_instance

theorem classObject_target_finite (C : RightReflectionChain N)
    (hN : Module.finrank N.RightRingᵐᵒᵖ N.Space = 1) (i : ClassIndex) :
    FiniteDimensional N.RightRingᵐᵒᵖ (classObject.{u,v} C i).Target := by
  induction i using Lex.rec with
  | h i =>
    rcases i with k | b
    · exact (preinjectiveFamily C k 0).targetFinite
    · cases b
      · apply Module.finite_of_finrank_pos
        have h : Module.finrank N.RightRingᵐᵒᵖ (tensorCanonicalProjective.{u,v} N).Target = 1 :=
          congrArg Prod.snd (canonicalProjective_dimension_vector.{u,v} N hN)
        change 0 < Module.finrank N.RightRingᵐᵒᵖ (tensorCanonicalProjective.{u,v} N).Target
        rw [h]
        exact Nat.one_pos
      · apply Module.finite_of_finrank_pos
        change 0 < Module.finrank N.RightRingᵐᵒᵖ (tensorSimpleTarget.{u,v} N).Target
        rw [simpleTarget_target_finrank]
        exact Nat.one_pos

theorem classObject_indecomposable (C : RightReflectionChain N) (i : ClassIndex) :
    Indecomposable (classObject.{u,v} C i) := by
  induction i using Lex.rec with
  | h i =>
    rcases i with k | b
    · exact preinjectiveFamily_indecomposable C k 0
    · cases b
      · exact tensorCanonicalProjective_indecomposable N
      · exact tensorSimpleTarget_indecomposable N

/-- Every member of the list has a division endomorphism ring. -/
theorem classObject_endRing_division (C : RightReflectionChain N) (i : ClassIndex) :
    ∃ (K : Type u) (_ : DivisionRing K), Nonempty (End (classObject.{u,v} C i) ≃+* K) := by
  induction i using Lex.rec with
  | h i =>
    rcases i with k | b
    · exact preinjectiveFamily_endo_division C k 0
    · cases b
      · exact ⟨N.LeftRing, inferInstance, ⟨tensorCanonicalProjectiveEndRingEquiv N⟩⟩
      · exact ⟨N.RightRing, inferInstance, ⟨tensorSimpleTargetEndRingEquiv N⟩⟩

/-- Manuscript `prop:class`, completeness: every finite-dimensional indecomposable
representation is isomorphic to a member of the list. -/
theorem classObject_complete (C : RightReflectionChain N)
    (hN : Module.finrank N.RightRingᵐᵒᵖ N.Space = 1)
    (M : TensorRepresentation.{u,max u v,max u v} N)
    [FiniteDimensional N.LeftRingᵐᵒᵖ M.Source]
    [FiniteDimensional N.RightRingᵐᵒᵖ M.Target] (hM : Indecomposable M) :
    ∃ i : ClassIndex, Nonempty (M ≅ classObject.{u,v} C i) := by
  rcases finiteIndecomposable_classification C hN M hM with hS | hT | hP | ⟨k, _, hI⟩
  · exact ⟨toLex (Sum.inl 0), hS⟩
  · exact ⟨toLex (Sum.inr true), hT⟩
  · exact ⟨toLex (Sum.inr false), hP⟩
  · exact ⟨toLex (Sum.inl k), hI⟩

/-- Manuscript `prop:class`, irredundancy: distinct members of the list are not isomorphic.
They are separated by their dimension vectors `(k+1,k)`, `(1,1)` and `(0,1)`. -/
theorem classObject_irredundant (C : RightReflectionChain N)
    (hN : Module.finrank N.RightRingᵐᵒᵖ N.Space = 1) {i j : ClassIndex}
    (e : Nonempty (classObject.{u,v} C i ≅ classObject.{u,v} C j)) : i = j := by
  obtain ⟨e⟩ := e
  have hs := tensorIso_source_finrank e
  have ht := tensorIso_target_finrank e
  rcases classObject_source_finrank_pos_or C hN i with ⟨k, rfl, hk1, hk2⟩ | ⟨rfl, h1, h2⟩ |
      ⟨rfl, h1, h2⟩ <;>
    rcases classObject_source_finrank_pos_or C hN j with ⟨l, rfl, hl1, hl2⟩ | ⟨rfl, h1', h2'⟩ |
      ⟨rfl, h1', h2'⟩ <;>
    first
    | rfl
    | (have := hs; have := ht; omega)
    | (rw [show k = l by omega])

/-- Manuscript `prop:class`, ordered Hom vanishing: `Hom(C, C') = 0` whenever `C` precedes `C'`
in the order `E₁ < I₁ < I₂ < ⋯ < P < E₂`. -/
theorem classObject_hom_subsingleton (C : RightReflectionChain N)
    (hN : Module.finrank N.RightRingᵐᵒᵖ N.Space = 1) {i j : ClassIndex} (hij : i < j) :
    Subsingleton (classObject.{u,v} C i ⟶ classObject.{u,v} C j) := by
  letI : FiniteDimensional N.RightRingᵐᵒᵖ N.Space := C.finite 0
  induction i using Lex.rec with
  | h i =>
  induction j using Lex.rec with
  | h j =>
  rcases i with k | b <;> rcases j with l | c
  · -- `I_k → I_l` with `k < l`.
    have hkl : k < l := Sum.Lex.inl_lt_inl_iff.mp hij
    let Y := (preinjectiveFamily.{u,v} C l 0).obj
    exact @preinjectiveFamily_hom_subsingleton.{u,v} N C k 0 Y
      (preinjectiveFamily C l 0).sourceFinite (preinjectiveFamily C l 0).targetFinite
      (preinjectiveFamily_indecomposable C l 0)
      (by rw [(preinjectiveFamily C l 0).source_finrank, (preinjectiveFamily C l 0).target_finrank]
          omega)
      (by rw [(preinjectiveFamily C l 0).source_finrank, (preinjectiveFamily C l 0).target_finrank]
          simpa using hkl)
  · cases c
    · -- `I_k → P`.
      let P := tensorCanonicalProjective.{u,v} N
      have hs : Module.finrank N.LeftRingᵐᵒᵖ P.Source = 1 :=
        congrArg Prod.fst (canonicalProjective_dimension_vector N hN)
      have ht : Module.finrank N.RightRingᵐᵒᵖ P.Target = 1 :=
        congrArg Prod.snd (canonicalProjective_dimension_vector N hN)
      exact @preinjectiveFamily_hom_subsingleton.{u,v} N C k 0 P
        (classObject_source_finite C hN (toLex (Sum.inr false)))
        (classObject_target_finite C hN (toLex (Sum.inr false)))
        (tensorCanonicalProjective_indecomposable N)
        (by change Module.finrank N.RightRingᵐᵒᵖ P.Target ≤ Module.finrank N.LeftRingᵐᵒᵖ P.Source
            rw [hs, ht])
        (by change k * (Module.finrank N.LeftRingᵐᵒᵖ P.Source -
                Module.finrank N.RightRingᵐᵒᵖ P.Target) < Module.finrank N.RightRingᵐᵒᵖ P.Target
            rw [hs, ht]; simp)
    · -- `I_k → E₂`: the arrow of `I_k` is surjective.
      exact ⟨fun f g =>
        (tensorHomToSimpleTarget_eq_zero N (preinjectiveRepresentation C k)
          (preinjectiveFamily_arrow_surjective C k 0) f).trans
        (tensorHomToSimpleTarget_eq_zero N (preinjectiveRepresentation C k)
          (preinjectiveFamily_arrow_surjective C k 0) g).symm⟩
  · exact absurd hij (not_lt.mpr (le_of_lt (Sum.Lex.inl_lt_inr l b)))
  · have hbc : b < c := Sum.Lex.inr_lt_inr_iff.mp hij
    cases b <;> cases c
    · exact absurd hbc (lt_irrefl _)
    · -- `P → E₂`: the arrow of `P` is bijective.
      exact ⟨fun f g =>
        (tensorHomToSimpleTarget_eq_zero N (tensorCanonicalProjective N)
          (canonicalProjective_tensorArrow_bijective N).2 f).trans
        (tensorHomToSimpleTarget_eq_zero N (tensorCanonicalProjective N)
          (canonicalProjective_tensorArrow_bijective N).2 g).symm⟩
    · exact absurd hbc (by decide)
    · exact absurd hbc (lt_irrefl _)

end
end QuantumFlags

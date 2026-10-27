import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Projection

/-!
# Finite direct sum decompositions over a left artinian ring

First sentence of the proof of manuscript `lem:decomp` (source line 144): every finitely generated
module over an artinian ring is a finite direct sum of the listed indecomposable modules.
Right modules over `Λ` are left modules over `Λᵐᵒᵖ`, so the statement is made for left modules
over an arbitrary left artinian ring `R`.

A module is indecomposable when it is nonzero and has no decomposition into two nonzero
complementary submodules.  The proof is well-founded induction on submodules, which is available
because a finitely generated module over an artinian ring is artinian.
-/

namespace QuantumFlags
noncomputable section
universe u w

/-- A module is indecomposable if it is nonzero and is not the internal direct sum of two
nonzero submodules. -/
def ModuleIndecomposable (R : Type u) [Ring R] (M : Type*) [AddCommGroup M] [Module R M] : Prop :=
  Nontrivial M ∧ ∀ A B : Submodule R M, IsCompl A B → A = ⊥ ∨ B = ⊥

variable {R : Type u} [Ring R]

/-- A nonzero module that is not indecomposable has two nonzero complementary submodules. -/
theorem exists_nontrivial_isCompl_of_not_indecomposable {M : Type*} [AddCommGroup M] [Module R M]
    (hnt : Nontrivial M) (h : ¬ ModuleIndecomposable R M) :
    ∃ A B : Submodule R M, IsCompl A B ∧ A ≠ ⊥ ∧ B ≠ ⊥ := by
  by_contra hne
  apply h
  refine ⟨hnt, fun A B hAB => ?_⟩
  by_contra hAB'
  push Not at hAB'
  exact hne ⟨A, B, hAB, hAB'⟩

/-- A summand of a nonzero complement is a proper submodule of the ambient submodule. -/
theorem map_subtype_lt_of_isCompl {M : Type*} [AddCommGroup M] [Module R M]
    (S : Submodule R M) {A B : Submodule R S} (hAB : IsCompl A B) (hB : B ≠ ⊥) :
    A.map S.subtype < S := by
  refine lt_of_le_of_ne (Submodule.map_subtype_le S A) ?_
  intro hEq
  obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hB
  have hbS : (b : M) ∈ A.map S.subtype := by rw [hEq]; exact b.property
  obtain ⟨a, ha, hab⟩ := Submodule.mem_map.mp hbS
  have : a = b := Subtype.ext hab
  subst this
  have hmem : a ∈ A ⊓ B := ⟨ha, hb⟩
  rw [hAB.inf_eq_bot, Submodule.mem_bot] at hmem
  exact hb0 hmem

variable {I : Type*} (X : I → Type w) [∀ i, AddCommGroup (X i)] [∀ i, Module R (X i)]

/-- Every finitely generated module over a left artinian ring is isomorphic to a finite direct
sum (a finite product) of members of a complete list of finitely generated indecomposables. -/
theorem finite_decomposition [IsArtinianRing R]
    (hcomplete : ∀ (F : Type w) [AddCommGroup F] [Module R F], Module.Finite R F →
      ModuleIndecomposable R F → ∃ i, Nonempty (F ≃ₗ[R] X i))
    (F : Type w) [AddCommGroup F] [Module R F] [Module.Finite R F] :
    ∃ (κ : Type) (_ : Fintype κ) (β : κ → I), Nonempty (F ≃ₗ[R] ((k : κ) → X (β k))) := by
  classical
  haveI : IsArtinian R F := inferInstance
  suffices h : ∀ S : Submodule R F, Module.Finite R S →
      ∃ (κ : Type) (_ : Fintype κ) (β : κ → I), Nonempty (S ≃ₗ[R] ((k : κ) → X (β k))) by
    obtain ⟨κ, hκ, β, ⟨e⟩⟩ := h ⊤ inferInstance
    exact ⟨κ, hκ, β, ⟨(Submodule.topEquiv).symm.trans e⟩⟩
  intro S
  induction S using WellFoundedLT.induction with
  | _ S ih =>
    intro hS
    by_cases hsub : Subsingleton S
    · refine ⟨Empty, inferInstance, Empty.elim, ⟨LinearEquiv.ofSubsingleton _ _⟩⟩
    rw [not_subsingleton_iff_nontrivial] at hsub
    by_cases hind : ModuleIndecomposable R S
    · obtain ⟨i, ⟨e⟩⟩ := hcomplete S hS hind
      exact ⟨Unit, inferInstance, fun _ => i,
        ⟨e.trans (LinearEquiv.funUnique Unit R (X i)).symm⟩⟩
    obtain ⟨A, B, hAB, hA, hB⟩ := exists_nontrivial_isCompl_of_not_indecomposable hsub hind
    have hAfin : Module.Finite R A :=
      Module.Finite.of_surjective (Submodule.linearProjOfIsCompl A B hAB)
        (Submodule.linearProjOfIsCompl_surjective hAB)
    have hBfin : Module.Finite R B :=
      Module.Finite.of_surjective (Submodule.linearProjOfIsCompl B A hAB.symm)
        (Submodule.linearProjOfIsCompl_surjective hAB.symm)
    let eA := Submodule.equivMapOfInjective S.subtype S.injective_subtype A
    let eB := Submodule.equivMapOfInjective S.subtype S.injective_subtype B
    have hA'fin : Module.Finite R (A.map S.subtype) := Module.Finite.equiv eA
    have hB'fin : Module.Finite R (B.map S.subtype) := Module.Finite.equiv eB
    obtain ⟨κ₁, h₁, β₁, ⟨e₁⟩⟩ := ih _ (map_subtype_lt_of_isCompl S hAB hB) hA'fin
    obtain ⟨κ₂, h₂, β₂, ⟨e₂⟩⟩ := ih _ (map_subtype_lt_of_isCompl S hAB.symm hA) hB'fin
    refine ⟨κ₁ ⊕ κ₂, inferInstance, Sum.elim β₁ β₂, ⟨?_⟩⟩
    exact (Submodule.prodEquivOfIsCompl A B hAB).symm.trans
      (((eA.trans e₁).prodCongr (eB.trans e₂)).trans
        (LinearEquiv.sumPiEquivProdPi R κ₁ κ₂ (fun s => X (Sum.elim β₁ β₂ s))).symm)

end
end QuantumFlags

import QuantumFlags.FiniteDecomposition
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Pure semisimplicity and representation type

Definitions from the manuscript, Section 2.1 (source line 75), and their invariance under ring
isomorphisms.

* A ring is right (left) pure semisimple if every right (left) module is a direct sum of finitely
  generated modules.  Right `Λ`-modules are modules over `Λᵐᵒᵖ`.  Modules range over a fixed
  universe `w`.
* A ring is of finite representation type if there are only finitely many isomorphism classes of
  finitely generated indecomposable right modules and only finitely many of left modules.
-/

namespace QuantumFlags
noncomputable section
open DirectSum
universe u u' w

/-- Every module over `S` (in the universe `w`) is a direct sum of finitely generated modules. -/
def EveryModuleDirectSumFG (S : Type u) [Ring S] : Prop :=
  ∀ (M : Type w) [AddCommGroup M] [Module S M],
    ∃ (κ : Type w) (Y : κ → Type w) (_ : ∀ k, AddCommGroup (Y k)) (_ : ∀ k, Module S (Y k)),
      (∀ k, Module.Finite S (Y k)) ∧ Nonempty (M ≃ₗ[S] ⨁ k, Y k)

/-- A ring `Λ` is right pure semisimple if every right `Λ`-module is a direct sum of finitely
generated right `Λ`-modules. -/
abbrev IsRightPureSemisimple (Λ : Type u) [Ring Λ] : Prop := EveryModuleDirectSumFG.{u,w} Λᵐᵒᵖ

/-- A ring `Λ` is left pure semisimple if every left `Λ`-module is a direct sum of finitely
generated left `Λ`-modules. -/
abbrev IsLeftPureSemisimple (Λ : Type u) [Ring Λ] : Prop := EveryModuleDirectSumFG.{u,w} Λ

/-- Only finitely many isomorphism classes of finitely generated indecomposable `S`-modules. -/
def FinitelyManyIndecomposables (S : Type u) [Ring S] : Prop :=
  ∃ (n : ℕ) (X : Fin n → Type w) (_ : ∀ i, AddCommGroup (X i)) (_ : ∀ i, Module S (X i)),
    ∀ (F : Type w) [AddCommGroup F] [Module S F], Module.Finite S F →
      ModuleIndecomposable S F → ∃ i, Nonempty (F ≃ₗ[S] X i)

/-- A ring is of finite representation type if it has only finitely many isomorphism classes of
finitely generated indecomposable right modules and only finitely many of left modules. -/
def IsFiniteRepresentationType (Λ : Type u) [Ring Λ] : Prop :=
  FinitelyManyIndecomposables.{u,w} Λᵐᵒᵖ ∧ FinitelyManyIndecomposables.{u,w} Λ

/-- An infinite family of pairwise nonisomorphic finitely generated indecomposable modules rules
out finitely many isomorphism classes. -/
theorem not_finitelyManyIndecomposables {S : Type u} [Ring S] (Y : ℕ → Type w)
    [∀ k, AddCommGroup (Y k)] [∀ k, Module S (Y k)] (hfin : ∀ k, Module.Finite S (Y k))
    (hind : ∀ k, ModuleIndecomposable S (Y k))
    (hne : ∀ k l, k ≠ l → ¬ Nonempty (Y k ≃ₗ[S] Y l)) :
    ¬ FinitelyManyIndecomposables.{u,w} S := by
  rintro ⟨n, X, _, _, h⟩
  choose i hi using fun k => h (Y k) (hfin k) (hind k)
  obtain ⟨k, l, hkl, heq⟩ := Finite.exists_ne_map_eq_of_infinite i
  obtain ⟨e₁⟩ := hi k
  obtain ⟨e₂⟩ := hi l
  rw [heq] at e₁
  exact hne k l hkl ⟨e₁.trans e₂.symm⟩

section Transport

variable {S : Type u} {S' : Type u'} [Ring S] [Ring S'] (φ : S ≃+* S')

/-- Scalars of an `S'`-module restricted along a ring isomorphism `φ : S ≃+* S'`. -/
abbrev restrictedModule (M : Type*) [AddCommGroup M] [Module S' M] : Module S M :=
  Module.compHom M φ.toRingHom

theorem restricted_smul (M : Type*) [AddCommGroup M] [Module S' M] (s : S) (x : M) :
    letI := restrictedModule φ M
    s • x = φ s • x := rfl

/-- An `S'`-module viewed through the inverse isomorphism. -/
theorem restricted_symm_smul (M : Type*) [AddCommGroup M] [iS : Module S M] (s' : S') (x : M) :
    letI := restrictedModule φ.symm M
    s' • x = φ.symm s' • x := rfl

/-- Finite generation is invariant under restriction along a ring isomorphism. -/
theorem restricted_finite (M : Type*) [AddCommGroup M] [Module S M] [hM : Module.Finite S M] :
    letI := restrictedModule φ.symm M
    Module.Finite S' M := by
  letI := restrictedModule φ.symm M
  obtain ⟨s, hs⟩ := hM.fg_top
  refine ⟨⟨s, ?_⟩⟩
  rw [eq_top_iff]
  rintro x -
  have hx : x ∈ Submodule.span S (s : Set M) := by rw [hs]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span hy
  | zero => exact Submodule.zero_mem _
  | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
  | smul a y _ hy =>
    have : a • y = φ a • y := by
      change a • y = φ.symm (φ a) • y
      rw [RingEquiv.symm_apply_apply]
    rw [this]
    exact Submodule.smul_mem _ _ hy

/-- Indecomposability is invariant under restriction along a ring isomorphism. -/
theorem restricted_indecomposable (M : Type*) [AddCommGroup M] [Module S M]
    (hM : ModuleIndecomposable S M) :
    letI := restrictedModule φ.symm M
    ModuleIndecomposable S' M := by
  letI := restrictedModule φ.symm M
  obtain ⟨hnt, hc⟩ := hM
  refine ⟨hnt, fun A B hAB => ?_⟩
  have hsmul : ∀ (a : S) (y : M), a • y = φ a • y := fun a y => by
    change a • y = φ.symm (φ a) • y
    rw [RingEquiv.symm_apply_apply]
  let toS : Submodule S' M → Submodule S M := fun A =>
    { carrier := A
      add_mem' := A.add_mem
      zero_mem' := A.zero_mem
      smul_mem' := fun a y hy => by rw [hsmul]; exact A.smul_mem _ hy }
  have hcompl : IsCompl (toS A) (toS B) := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x hxA hxB
      exact (Submodule.disjoint_def.mp hAB.disjoint) x hxA hxB
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp
        (show x ∈ A ⊔ B by rw [hAB.sup_eq_top]; trivial)
      exact Submodule.add_mem_sup ha hb
  rcases hc _ _ hcompl with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ toS A := hx
    rw [h] at this
    exact this
  · right
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ toS B := hx
    rw [h] at this
    exact this

/-- An `S'`-linear equivalence between restricted modules is `S`-linear. -/
def restrictedLinearEquiv {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module S' M]
    [Module S' N] (e : M ≃ₗ[S'] N) :
    letI := restrictedModule φ M
    letI := restrictedModule φ N
    M ≃ₗ[S] N :=
  letI := restrictedModule φ M
  letI := restrictedModule φ N
  { e.toAddEquiv with
    map_smul' := fun s x => e.map_smul (φ s) x }

include φ in
/-- Every module being a direct sum of finitely generated modules is invariant under ring
isomorphisms. -/
theorem everyModuleDirectSumFG_of_ringEquiv (h : EveryModuleDirectSumFG.{u,w} S) :
    EveryModuleDirectSumFG.{u',w} S' := by
  intro M _ _
  letI := restrictedModule φ M
  obtain ⟨κ, Y, iG, iM, hfin, ⟨e⟩⟩ := h M
  letI iM' : ∀ k, Module S' (Y k) := fun k => restrictedModule φ.symm (Y k)
  refine ⟨κ, Y, iG, iM', fun k => restricted_finite φ (Y k), ⟨?_⟩⟩
  exact { e.toAddEquiv with
    map_smul' := fun s' x => by
      have h1 : s' • x = φ.symm s' • x := by
        change s' • x = φ (φ.symm s') • x
        rw [RingEquiv.apply_symm_apply]
      change e.toAddEquiv (s' • x) = s' • e.toAddEquiv x
      rw [h1]
      change e (φ.symm s' • x) = _
      rw [e.map_smul]
      ext k
      rfl }

include φ in
/-- Finitely many isomorphism classes of finitely generated indecomposables pass back along a
ring isomorphism. -/
theorem finitelyManyIndecomposables_of_ringEquiv :
    FinitelyManyIndecomposables.{u',w} S' → FinitelyManyIndecomposables.{u,w} S := by
  rintro ⟨n, X, iG, iM, h⟩
  refine ⟨n, X, iG, fun i => restrictedModule φ (X i), ?_⟩
  intro F _ _ hfin hind
  letI := restrictedModule φ.symm F
  obtain ⟨i, ⟨e⟩⟩ := h F (restricted_finite φ F) (restricted_indecomposable φ F hind)
  letI : Module S (X i) := restrictedModule φ (X i)
  refine ⟨i, ⟨{ e.toAddEquiv with map_smul' := fun s x => ?_ }⟩⟩
  have hx : s • x = φ s • x := by
    change s • x = φ.symm (φ s) • x
    rw [RingEquiv.symm_apply_apply]
  change e (s • x) = φ s • e x
  rw [hx, e.map_smul]

end Transport

end
end QuantumFlags

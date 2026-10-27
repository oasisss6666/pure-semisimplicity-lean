import QuantumFlags.FiniteDecomposition
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Indecomposable modules

Two comparisons used to apply the decomposition lemma to the classification:

* a nonzero module whose nonzero endomorphisms are invertible is indecomposable;
* in any choice of binary biproducts on `ModuleCat R`, an indecomposable module is a
  categorically indecomposable object.
-/

namespace QuantumFlags
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u w

variable {R : Type u} [Ring R]

/-- A nonzero module with division endomorphism ring is indecomposable. -/
theorem moduleIndecomposable_of_isUnit {M : Type*} [AddCommGroup M] [Module R M]
    [Nontrivial M] (hdiv : ∀ f : Module.End R M, f ≠ 0 → IsUnit f) :
    ModuleIndecomposable R M := by
  refine ⟨inferInstance, fun A B hAB => ?_⟩
  let p : Module.End R M := A.subtype ∘ₗ Submodule.linearProjOfIsCompl A B hAB
  have hpA : ∀ a ∈ A, p a = a := fun a ha => by
    exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hAB ⟨a, ha⟩)
  by_cases hp : p = 0
  · left
    rw [Submodule.eq_bot_iff]
    intro a ha
    rw [← hpA a ha, hp, LinearMap.zero_apply]
  · right
    have hsurj : Function.Surjective p := (Module.End.isUnit_iff p).mp (hdiv p hp) |>.2
    rw [Submodule.eq_bot_iff]
    intro b hb
    obtain ⟨x, rfl⟩ := hsurj b
    have hmem : p x ∈ A ⊓ B := ⟨Submodule.coe_mem _, hb⟩
    rw [hAB.inf_eq_bot, Submodule.mem_bot] at hmem
    exact hmem

variable [HasBinaryBiproducts (ModuleCat.{w} R)]

/-- An indecomposable module is indecomposable as an object of `ModuleCat R`. -/
theorem indecomposable_of_moduleIndecomposable (F : ModuleCat.{w} R)
    (hF : ModuleIndecomposable R F) : Indecomposable F := by
  obtain ⟨hnt, hcompl⟩ := hF
  refine ⟨fun hz => ?_, fun Y Z e => ?_⟩
  · haveI := ModuleCat.subsingleton_of_isZero hz
    exact not_subsingleton F inferInstance
  let i₁ : Y ⟶ F := biprod.inl ≫ e.inv
  let p₁ : F ⟶ Y := e.hom ≫ biprod.fst
  let i₂ : Z ⟶ F := biprod.inr ≫ e.inv
  let p₂ : F ⟶ Z := e.hom ≫ biprod.snd
  have h₁₁ : i₁ ≫ p₁ = 𝟙 Y := by simp [i₁, p₁]
  have h₂₂ : i₂ ≫ p₂ = 𝟙 Z := by simp [i₂, p₂]
  have h₂₁ : i₂ ≫ p₁ = 0 := by simp [i₂, p₁]
  have htot : p₁ ≫ i₁ + p₂ ≫ i₂ = 𝟙 F := by
    have h : p₁ ≫ i₁ + p₂ ≫ i₂ =
        e.hom ≫ (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) ≫ e.inv := by
      simp only [i₁, p₁, i₂, p₂, Preadditive.add_comp, Preadditive.comp_add, Category.assoc]
    rw [h, biprod.total, Category.id_comp, Iso.hom_inv_id]
  have e₁₁ : ∀ y, p₁.hom (i₁.hom y) = y := fun y => by
    simpa using congrArg (fun φ => φ.hom y) h₁₁
  have e₂₂ : ∀ z, p₂.hom (i₂.hom z) = z := fun z => by
    simpa using congrArg (fun φ => φ.hom z) h₂₂
  have e₂₁ : ∀ z, p₁.hom (i₂.hom z) = 0 := fun z => by
    simpa using congrArg (fun φ => φ.hom z) h₂₁
  have etot : ∀ x, i₁.hom (p₁.hom x) + i₂.hom (p₂.hom x) = x := fun x => by
    simpa using congrArg (fun φ => φ.hom x) htot
  have hc : IsCompl (LinearMap.range i₁.hom) (LinearMap.range i₂.hom) := by
    constructor
    · rw [Submodule.disjoint_def]
      rintro x ⟨y, rfl⟩ ⟨z, hz⟩
      have : y = 0 := by rw [← e₁₁ y, ← hz, e₂₁]
      rw [this, map_zero]
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      rw [← etot x]
      exact Submodule.add_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩
  rcases hcompl _ _ hc with h | h
  · left
    rw [ModuleCat.isZero_iff_subsingleton]
    refine ⟨fun a b => ?_⟩
    have ha : i₁.hom a = 0 := by
      rw [← Submodule.mem_bot R, ← h]; exact ⟨a, rfl⟩
    have hb : i₁.hom b = 0 := by
      rw [← Submodule.mem_bot R, ← h]; exact ⟨b, rfl⟩
    rw [← e₁₁ a, ← e₁₁ b, ha, hb]
  · right
    rw [ModuleCat.isZero_iff_subsingleton]
    refine ⟨fun a b => ?_⟩
    have ha : i₂.hom a = 0 := by
      rw [← Submodule.mem_bot R, ← h]; exact ⟨a, rfl⟩
    have hb : i₂.hom b = 0 := by
      rw [← Submodule.mem_bot R, ← h]; exact ⟨b, rfl⟩
    rw [← e₂₂ a, ← e₂₂ b, ha, hb]

end
end QuantumFlags

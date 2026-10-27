import QuantumFlags.FiniteDecomposition
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Field.Basic

/-!
# The decomposition lemma

Manuscript `lem:decomp` (source lines 139-153).  Let `Λ` be a right artinian ring and let
`(X_α)_{α ∈ I}`, indexed by a well-ordered set, be representatives of the isomorphism classes of
finitely generated indecomposable right `Λ`-modules, with division endomorphism rings and
`Hom(X_α, X_β) = 0` for `α < β`.  Then every right `Λ`-module is a direct sum of modules `X_α`.

Right `Λ`-modules are left `Λᵐᵒᵖ`-modules, so the lemma is stated for left modules over a left
artinian ring `R`.

The proof follows the manuscript.  `W_α` is the span of the maps `X_α → M` factoring through an
earlier `X_β`, `Hom(X_α, M)` is a right `End(X_α)`-module by precomposition, and the maps
`f_{α i}` are lifts of a basis of `Hom(X_α, M) / W_α`.  Every map from some `X_α` lifts along
the induced map `π : ⨁ X_α → M` by well-founded induction, hence every map from a finitely
generated module lifts, and `π` is surjective.  A map `X_α → ker π` has no components of type
`≥ α`.  For the injectivity of `π`, the endomorphism `e = ι - w p₀` of the manuscript satisfies
`e z = z` while strictly lowering types; the manuscript concludes by nilpotency of `e` on a finite
coordinate summand, and here the same fact is used through a coordinate of `z` of maximal type,
which `e z = z` would force to come from a coordinate of strictly larger type.
-/

namespace QuantumFlags
noncomputable section
open DirectSum
universe u v w wx wm

variable {R : Type u} [Ring R]

/-- `Hom(X, M)` is a right `End(X)`-module under precomposition. -/
local instance precompositionModule {X : Type wx} {M : Type wm} [AddCommGroup X] [Module R X]
    [AddCommGroup M] [Module R M] : Module (Module.End R X)ᵐᵒᵖ (X →ₗ[R] M) where
  smul e f := f ∘ₗ e.unop
  one_smul f := LinearMap.comp_id f
  mul_smul _ _ _ := rfl
  smul_zero _ := LinearMap.zero_comp _
  smul_add _ _ _ := LinearMap.add_comp _ _ _
  add_smul _ _ _ := LinearMap.comp_add _ _ _
  zero_smul f := LinearMap.comp_zero f

section Precomposition

variable (X : Type wx) (M : Type wm) [AddCommGroup X] [Module R X] [AddCommGroup M] [Module R M]

theorem precomposition_smul (e : (Module.End R X)ᵐᵒᵖ) (f : X →ₗ[R] M) :
    e • f = f ∘ₗ e.unop := rfl

/-- If `End(X)` is a division ring, then modulo any `End(X)`-submodule `W` of `Hom(X, M)` there
is a family of maps whose classes form a basis: every map is a finite combination of them modulo
`W`, and a finite combination lying in `W` has vanishing coefficients. -/
theorem exists_basis_modulo [Nontrivial X]
    (hdiv : ∀ f : Module.End R X, f ≠ 0 → IsUnit f)
    (W : Submodule (Module.End R X)ᵐᵒᵖ (X →ₗ[R] M)) :
    ∃ (J : Type (max wx wm)) (f : J → (X →ₗ[R] M)),
      (∀ g : X →ₗ[R] M, ∃ (s : Finset J) (d : J → Module.End R X),
        g - ∑ j ∈ s, f j ∘ₗ d j ∈ W) ∧
      (∀ (s : Finset J) (d : J → Module.End R X),
        ∑ j ∈ s, f j ∘ₗ d j ∈ W → ∀ j ∈ s, d j = 0) := by
  classical
  let K := (Module.End R X)ᵐᵒᵖ
  have hunit : ∀ a : K, IsUnit a ∨ a = 0 := by
    intro a
    by_cases ha : a = 0
    · exact Or.inr ha
    · left
      have h0 : a.unop ≠ 0 := fun h => ha (MulOpposite.unop_injective h)
      simpa using (hdiv a.unop h0).op
  letI : DivisionRing K := DivisionRing.ofIsUnitOrEqZero hunit
  let Q := (X →ₗ[R] M) ⧸ W
  let b := Module.Basis.ofVectorSpace K Q
  let f : Module.Basis.ofVectorSpaceIndex K Q → (X →ₗ[R] M) := fun j => Quotient.out (b j)
  have hf : ∀ j, W.mkQ (f j) = b j := fun j => Quotient.out_eq (b j)
  refine ⟨Module.Basis.ofVectorSpaceIndex K Q, f, ?_, ?_⟩
  · intro g
    let c := b.repr (W.mkQ g)
    refine ⟨c.support, fun j => (c j).unop, ?_⟩
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, sub_eq_zero]
    change W.mkQ g = W.mkQ (∑ j ∈ c.support, f j ∘ₗ (c j).unop)
    rw [map_sum]
    have hterm : ∀ j, W.mkQ (f j ∘ₗ (c j).unop) = c j • b j := by
      intro j
      rw [← hf j, ← map_smul]
      rfl
    simp_rw [hterm]
    have hrepr := b.linearCombination_repr (W.mkQ g)
    rw [Finsupp.linearCombination_apply, Finsupp.sum] at hrepr
    exact hrepr.symm
  · intro s d hs j hj
    have hzero : ∑ i ∈ s, MulOpposite.op (d i) • b i = 0 := by
      have h := (Submodule.Quotient.mk_eq_zero W).mpr hs
      change W.mkQ (∑ i ∈ s, f i ∘ₗ d i) = 0 at h
      rw [map_sum] at h
      refine Eq.trans ?_ h
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hf i, ← map_smul]
      rfl
    have h := (linearIndependent_iff'.mp b.linearIndependent) s _ hzero j hj
    exact MulOpposite.op_injective h

end Precomposition

variable {I : Type v} [LinearOrder I] (X : I → Type w)
  [∀ i, AddCommGroup (X i)] [∀ i, Module R (X i)]

theorem component_apply_eq {κ : Type*} {Y : κ → Type*} [∀ c, AddCommGroup (Y c)]
    [∀ c, Module R (Y c)] (c : κ) (y : ⨁ c, Y c) : component R κ Y c y = y c := rfl

theorem component_lof_of_ne {κ : Type*} [DecidableEq κ] {Y : κ → Type*} [∀ c, AddCommGroup (Y c)]
    [∀ c, Module R (Y c)] {c c' : κ} (y : Y c) (h : c ≠ c') :
    component R κ Y c' (lof R κ Y c y) = 0 := by
  rw [DirectSum.component.of, dif_neg h]

/-- A linear map out of a finitely generated module into a direct sum has its image in finitely
many coordinates. -/
theorem exists_finset_component_eq_zero {κ : Type*} {Y : κ → Type*} [∀ c, AddCommGroup (Y c)]
    [∀ c, Module R (Y c)] {Z : Type*} [AddCommGroup Z] [Module R Z] [Module.Finite R Z]
    (h : Z →ₗ[R] ⨁ c, Y c) :
    ∃ S : Finset κ, ∀ c ∉ S, component R κ Y c ∘ₗ h = 0 := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := Z)
  refine ⟨s.biUnion fun z => (h z).support, fun c hc => ?_⟩
  have hle : Submodule.span R (s : Set Z) ≤ LinearMap.ker (component R κ Y c ∘ₗ h) := by
    rw [Submodule.span_le]
    intro x hx
    have hnot : c ∉ (h x).support := fun hmem =>
      hc (Finset.mem_biUnion.mpr ⟨x, hx, hmem⟩)
    rw [DFinsupp.notMem_support_iff] at hnot
    exact hnot
  apply LinearMap.ext
  intro z
  have hz : z ∈ Submodule.span R (s : Set Z) := by rw [hs]; trivial
  exact LinearMap.mem_ker.mp (hle hz)

/-- Expansion of a linear map into a direct sum along a finite set containing its support. -/
theorem eq_sum_lof_component {κ : Type*} [DecidableEq κ] {Y : κ → Type*} [∀ c, AddCommGroup (Y c)]
    [∀ c, Module R (Y c)] {Z : Type*} [AddCommGroup Z] [Module R Z]
    (h : Z →ₗ[R] ⨁ c, Y c) (S : Finset κ) (hS : ∀ c ∉ S, component R κ Y c ∘ₗ h = 0) :
    h = ∑ c ∈ S, lof R κ Y c ∘ₗ (component R κ Y c ∘ₗ h) := by
  apply LinearMap.ext
  intro z
  apply DirectSum.ext_component R
  intro c'
  rw [LinearMap.sum_apply, map_sum]
  simp only [LinearMap.comp_apply]
  by_cases hc' : c' ∈ S
  · rw [Finset.sum_eq_single c']
    · rw [DirectSum.component.lof_self]
    · intro c _ hne
      exact component_lof_of_ne _ hne
    · intro h'; exact absurd hc' h'
  · rw [Finset.sum_eq_zero]
    · exact congrArg (fun φ => φ z) (hS c' hc')
    · intro c hc
      exact component_lof_of_ne _ (fun he => hc' (he ▸ hc))

/-- Manuscript `lem:decomp`: over a left artinian ring, if `(X_α)` indexed by a well-ordered set
is a complete irredundant list of the finitely generated indecomposable modules, with division
endomorphism rings and `Hom(X_α, X_β) = 0` for `α < β`, then every module is isomorphic to a
direct sum of modules `X_α`. -/
theorem decomposition_lemma [IsArtinianRing R] [WellFoundedLT I]
    (hfin : ∀ i, Module.Finite R (X i))
    (hind : ∀ i, ModuleIndecomposable R (X i))
    (hcomplete : ∀ (F : Type w) [AddCommGroup F] [Module R F], Module.Finite R F →
      ModuleIndecomposable R F → ∃ i, Nonempty (F ≃ₗ[R] X i))
    (_hirred : ∀ i j, Nonempty (X i ≃ₗ[R] X j) → i = j)
    (hdiv : ∀ i (f : Module.End R (X i)), f ≠ 0 → IsUnit f)
    (hvan : ∀ i j, i < j → ∀ f : X i →ₗ[R] X j, f = 0)
    (M : Type w) [AddCommGroup M] [Module R M] :
    ∃ (κ : Type (max v w)) (β : κ → I), Nonempty (M ≃ₗ[R] ⨁ k, X (β k)) := by
  classical
  -- `W α`: the maps `X α → M` factoring through an earlier `X β`.
  let W : ∀ α, Submodule (Module.End R (X α))ᵐᵒᵖ (X α →ₗ[R] M) := fun α =>
    Submodule.span _ {g | ∃ β, β < α ∧ ∃ (ψ : X α →ₗ[R] X β) (φ : X β →ₗ[R] M), g = φ ∘ₗ ψ}
  have hbasis := fun α => @exists_basis_modulo R _ (X α) M _ _ _ _ (hind α).1 (hdiv α) (W α)
  choose J f hspan hindep using hbasis
  let κ := Σ α, J α
  let B := ⨁ c : κ, X c.1
  let π : B →ₗ[R] M := toModule R κ M fun c => f c.1 c.2
  have hπ : ∀ c : κ, π ∘ₗ lof R κ (fun c => X c.1) c = f c.1 c.2 := fun c =>
    LinearMap.ext fun x => by
      rw [LinearMap.comp_apply]
      exact toModule_lof (M := fun c : κ => X c.1) R c x
  -- Every map from some `X α` lifts along `π`.
  have lift : ∀ α (g : X α →ₗ[R] M), ∃ h : X α →ₗ[R] B, π ∘ₗ h = g := by
    intro α
    induction α using WellFoundedLT.induction with
    | _ α ih =>
      let L : Submodule (Module.End R (X α))ᵐᵒᵖ (X α →ₗ[R] M) := {
        carrier := {g | ∃ h : X α →ₗ[R] B, π ∘ₗ h = g}
        add_mem' := by
          rintro g₁ g₂ ⟨h₁, rfl⟩ ⟨h₂, rfl⟩
          exact ⟨h₁ + h₂, LinearMap.comp_add _ _ _⟩
        zero_mem' := ⟨0, LinearMap.comp_zero _⟩
        smul_mem' := by
          rintro e g ⟨h, rfl⟩
          exact ⟨h ∘ₗ e.unop, rfl⟩ }
      have hW : W α ≤ L := by
        rw [Submodule.span_le]
        rintro g ⟨β, hβ, ψ, φ, rfl⟩
        obtain ⟨h, hh⟩ := ih β hβ φ
        exact ⟨h ∘ₗ ψ, by rw [← LinearMap.comp_assoc, hh]⟩
      intro g
      obtain ⟨s, d, hg⟩ := hspan α g
      have hsum : ∑ j ∈ s, f α j ∘ₗ d j ∈ L := by
        refine Submodule.sum_mem L fun j _ => ?_
        refine ⟨lof R κ (fun c => X c.1) ⟨α, j⟩ ∘ₗ d j, ?_⟩
        rw [← LinearMap.comp_assoc, hπ]
      have hmem : g ∈ L := by
        have := L.add_mem (hW hg) hsum
        rwa [sub_add_cancel] at this
      exact hmem
  -- Maps from finite products of listed modules lift.
  have liftPi : ∀ (κ' : Type) [Fintype κ'] (β : κ' → I) (g : ((k : κ') → X (β k)) →ₗ[R] M),
      ∃ h, π ∘ₗ h = g := by
    intro κ' _ β g
    choose h hh using fun k => lift (β k) (g ∘ₗ LinearMap.single R (fun k => X (β k)) k)
    refine ⟨∑ k, h k ∘ₗ LinearMap.proj k, ?_⟩
    apply LinearMap.ext
    intro x
    rw [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
    have hk : ∀ k, π (h k (x k)) = g (LinearMap.single R (fun k => X (β k)) k (x k)) :=
      fun k => congrArg (fun φ => φ (x k)) (hh k)
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, hk]
    rw [← map_sum]
    congr 1
    exact Finset.univ_sum_single x
  -- Inclusions of finitely generated submodules lift.
  have liftFG : ∀ V : Submodule R M, Module.Finite R V → ∃ h : V →ₗ[R] B, π ∘ₗ h = V.subtype := by
    intro V hV
    obtain ⟨κ', _, β, ⟨e⟩⟩ := finite_decomposition X hcomplete V
    obtain ⟨h, hh⟩ := liftPi κ' β (V.subtype ∘ₗ e.symm.toLinearMap)
    refine ⟨h ∘ₗ e.toLinearMap, ?_⟩
    rw [← LinearMap.comp_assoc, hh, LinearMap.comp_assoc, LinearEquiv.symm_comp,
      LinearMap.comp_id]
  -- `π` is surjective.
  have hsurj : Function.Surjective π := by
    intro m
    let V := Submodule.span R {m}
    haveI : Module.Finite R V := Module.Finite.span_singleton R m
    obtain ⟨h, hh⟩ := liftFG V inferInstance
    refine ⟨h ⟨m, Submodule.mem_span_singleton_self m⟩, ?_⟩
    exact congrArg (fun φ => φ ⟨m, Submodule.mem_span_singleton_self m⟩) hh
  -- A map `X α → ker π` has no components of type `≥ α`.
  have hker : ∀ α (h : X α →ₗ[R] B), π ∘ₗ h = 0 →
      ∀ c : κ, ¬ c.1 < α → component R κ (fun c => X c.1) c ∘ₗ h = 0 := by
    intro α h hh
    haveI := hfin α
    obtain ⟨S, hS⟩ := exists_finset_component_eq_zero h
    have hexp := eq_sum_lof_component h S hS
    -- Coordinates of type `> α` vanish.
    have hgt : ∀ c : κ, α < c.1 → component R κ (fun c => X c.1) c ∘ₗ h = 0 :=
      fun c hc => hvan α c.1 hc _
    -- The coordinates of type `α`.
    let d : J α → Module.End R (X α) := fun j => component R κ (fun c => X c.1) ⟨α, j⟩ ∘ₗ h
    let sα : Finset (J α) := S.preimage (Sigma.mk α) (fun _ _ _ _ h => sigma_mk_injective h)
    have hπh : π ∘ₗ h = ∑ c ∈ S, f c.1 c.2 ∘ₗ (component R κ (fun c => X c.1) c ∘ₗ h) := by
      apply LinearMap.ext
      intro x
      rw [LinearMap.comp_apply]
      conv_lhs => rw [hexp]
      rw [LinearMap.sum_apply, map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← hπ c]
      rfl
    have hsplit : ∑ c ∈ S, f c.1 c.2 ∘ₗ (component R κ (fun c => X c.1) c ∘ₗ h) =
        ∑ j ∈ sα, f α j ∘ₗ d j +
          ∑ c ∈ S.filter (fun c => c.1 ≠ α),
            f c.1 c.2 ∘ₗ (component R κ (fun c => X c.1) c ∘ₗ h) := by
      rw [← Finset.sum_filter_add_sum_filter_not S (fun c => c ∈ Set.range (Sigma.mk α))]
      congr 1
      · exact (Finset.sum_preimage' (Sigma.mk α) S _
          (fun c => f c.1 c.2 ∘ₗ (component R κ (fun c => X c.1) c ∘ₗ h))).symm
      · refine Finset.sum_congr ?_ fun _ _ => rfl
        ext c
        simp only [Finset.mem_filter, Set.mem_range, not_exists, ne_eq]
        constructor
        · rintro ⟨hc, hne⟩
          refine ⟨hc, fun heq => ?_⟩
          obtain ⟨a, j⟩ := c
          simp only at heq
          subst heq
          exact hne j rfl
        · rintro ⟨hc, hne⟩
          refine ⟨hc, fun j hj => hne ?_⟩
          rw [← hj]
    have hrest : ∑ c ∈ S.filter (fun c => c.1 ≠ α),
        f c.1 c.2 ∘ₗ (component R κ (fun c => X c.1) c ∘ₗ h) ∈ W α := by
      refine Submodule.sum_mem _ fun c hc => ?_
      rcases lt_or_gt_of_ne (Finset.mem_filter.mp hc).2 with hlt | hgt'
      · exact Submodule.subset_span ⟨c.1, hlt, _, f c.1 c.2, rfl⟩
      · rw [hgt c hgt', LinearMap.comp_zero]
        exact Submodule.zero_mem _
    have hmain : ∑ j ∈ sα, f α j ∘ₗ d j ∈ W α := by
      have h0 : ∑ j ∈ sα, f α j ∘ₗ d j = -(∑ c ∈ S.filter (fun c => c.1 ≠ α),
          f c.1 c.2 ∘ₗ (component R κ (fun c => X c.1) c ∘ₗ h)) := by
        rw [eq_neg_iff_add_eq_zero, ← hsplit, ← hπh, hh]
      rw [h0]
      exact Submodule.neg_mem _ hrest
    have hd : ∀ j, d j = 0 := by
      intro j
      by_cases hj : j ∈ sα
      · exact hindep α sα d hmain j hj
      · have hjS : (⟨α, j⟩ : κ) ∉ S := fun hmem => hj (Finset.mem_preimage.mpr hmem)
        exact hS _ hjS
    intro c hc
    rcases lt_or_eq_of_le (not_lt.mp hc) with hlt | heq
    · exact hgt c hlt
    · obtain ⟨a, j⟩ := c
      simp only at heq
      subst heq
      exact hd j
  -- `π` is injective.
  have hinj : Function.Injective π := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro z hz
    by_contra hz0
    rw [LinearMap.mem_ker] at hz
    let S₀ := z.support
    let ι₀ : ((c : S₀) → X c.1.1) →ₗ[R] B :=
      ∑ c : S₀, lof R κ (fun c => X c.1) c.1 ∘ₗ LinearMap.proj c
    let r₀ : B →ₗ[R] ((c : S₀) → X c.1.1) :=
      LinearMap.pi fun c => component R κ (fun c => X c.1) c.1
    haveI : ∀ c : S₀, Module.Finite R (X c.1.1) := fun c => hfin c.1.1
    let V := LinearMap.range (π ∘ₗ ι₀)
    obtain ⟨w', hw'⟩ := liftFG V inferInstance
    let e : B →ₗ[R] B := ι₀ ∘ₗ r₀ - w' ∘ₗ (π ∘ₗ ι₀).rangeRestrict ∘ₗ r₀
    have hπe : π ∘ₗ e = 0 := by
      apply LinearMap.ext
      intro b
      have hb : π (w' ((π ∘ₗ ι₀).rangeRestrict (r₀ b))) = π (ι₀ (r₀ b)) :=
        congrArg (fun φ => φ ((π ∘ₗ ι₀).rangeRestrict (r₀ b))) hw'
      simp only [e, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.zero_apply]
      rw [map_sub, hb, sub_self]
    have hι₀r₀ : ι₀ (r₀ z) = z := by
      apply DirectSum.ext_component R
      intro c'
      simp only [ι₀, r₀, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
        LinearMap.pi_apply, map_sum]
      by_cases hc' : c' ∈ S₀
      · rw [Finset.sum_eq_single ⟨c', hc'⟩]
        · rw [DirectSum.component.lof_self]
        · intro c _ hne
          exact component_lof_of_ne _ (fun he => hne (Subtype.ext he))
        · intro h'; exact absurd (Finset.mem_univ _) h'
      · rw [Finset.sum_eq_zero]
        · rw [component_apply_eq]
          exact (DFinsupp.notMem_support_iff.mp hc').symm
        · intro c _
          exact component_lof_of_ne _ (fun he => hc' (he ▸ c.2))
    have hez : e z = z := by
      have hr : (π ∘ₗ ι₀).rangeRestrict (r₀ z) = 0 := by
        apply Subtype.ext
        change π (ι₀ (r₀ z)) = 0
        rw [hι₀r₀, hz]
      simp only [e, LinearMap.sub_apply, LinearMap.comp_apply]
      rw [hr, map_zero, sub_zero, hι₀r₀]
    -- `e` strictly lowers types.
    have hlower : ∀ (b : B) (c' : κ), component R κ (fun c => X c.1) c' (e b) ≠ 0 →
        ∃ c ∈ b.support, c'.1 < c.1 := by
      intro b c' hne
      by_contra hno
      push Not at hno
      apply hne
      have hb : b = ∑ c ∈ b.support, lof R κ (fun c => X c.1) c (b c) := by
        conv_lhs => rw [← DirectSum.sum_support_of b]
        rfl
      rw [hb, map_sum, map_sum]
      refine Finset.sum_eq_zero fun c hc => ?_
      have hzero := hker c.1 (e ∘ₗ lof R κ (fun c => X c.1) c)
        (by rw [← LinearMap.comp_assoc, hπe, LinearMap.zero_comp]) c' (not_lt.mpr (hno c hc))
      exact congrArg (fun φ => φ (b c)) hzero
    have hne : z.support.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      apply hz0
      exact DFinsupp.support_eq_empty.mp hempty
    obtain ⟨c', hc', hmax⟩ := Finset.exists_max_image z.support (fun c => c.1) hne
    have hcz : component R κ (fun c => X c.1) c' (e z) ≠ 0 := by
      rw [hez, component_apply_eq]
      exact DFinsupp.mem_support_iff.mp hc'
    obtain ⟨c, hc, hlt⟩ := hlower z c' hcz
    exact absurd (hmax c hc) (not_le.mpr hlt)
  exact ⟨κ, fun c => c.1, ⟨(LinearEquiv.ofBijective π ⟨hinj, hsurj⟩).symm⟩⟩

end
end QuantumFlags

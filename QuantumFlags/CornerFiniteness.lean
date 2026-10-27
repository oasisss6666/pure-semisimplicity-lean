import QuantumFlags.CornerRegularSpaces

namespace QuantumFlags

noncomputable section

variable {A : Type*} {B : Type*} [Ring A] [Ring B]

theorem corner_finite_of_finite (f : A →ₙ+* B) (M : Type*) [AddCommGroup M] [Module B M]
    [Module.Finite B M]
    (h : letI := cornerFixedModule f B; Module.Finite A (cornerFixedGroup f B)) :
    letI := cornerFixedModule f M
    Module.Finite A (cornerFixedGroup f M) := by
  letI := cornerFixedModule f B
  letI := cornerFixedModule f M
  letI : Module.Finite A (cornerFixedGroup f B) := h
  obtain ⟨n,g,hg⟩ := Module.Finite.exists_fin' B M
  letI := cornerFixedModule f (Fin n → B)
  letI : Module.Finite A (cornerFixedGroup f (Fin n → B)) :=
    Module.Finite.equiv (cornerFixedPiEquiv f (Fin n) B).symm
  exact Module.Finite.of_surjective (cornerFixedMap f g) (cornerFixedMap_surjective f g hg)

theorem corner_coe_mem_of_span (f : A →ₙ+* B) (M : Type*) [AddCommGroup M] [Module B M]
    (s : Set (cornerFixedGroup f M))
    (hs : letI := cornerFixedModule f M; Submodule.span A s = ⊤)
    (V : Submodule B M) (hv : ∀ x ∈ s, (x : M) ∈ V) (x : cornerFixedGroup f M) :
    (x : M) ∈ V := by
  letI := cornerFixedModule f M
  let W : Submodule A (cornerFixedGroup f M) := {
    carrier := {x | (x : M) ∈ V}
    zero_mem' := V.zero_mem
    add_mem' := fun hx hy => V.add_mem hx hy
    smul_mem' := fun a y hy => V.smul_mem (f a) hy }
  have hle : Submodule.span A s ≤ W := Submodule.span_le.mpr hv
  rw [hs] at hle
  exact hle (Submodule.mem_top : x ∈ (⊤ : Submodule A (cornerFixedGroup f M)))

variable {D : Type*} [DivisionRing D]

theorem source_corner_finite_of_finite (H : Subfield D) (M : Type*) [AddCommGroup M]
    [Module (TriangularRing H)ᵐᵒᵖ M] [Module.Finite (TriangularRing H)ᵐᵒᵖ M] :
    FiniteDimensional Hᵐᵒᵖ (SourceCorner H M) :=
  corner_finite_of_finite (sourceCornerHom H) M (source_regular_finite H)

theorem target_corner_finite_of_finite (H : Subfield D) (M : Type*) [AddCommGroup M]
    [Module (TriangularRing H)ᵐᵒᵖ M] [Module.Finite (TriangularRing H)ᵐᵒᵖ M] :
    FiniteDimensional Dᵐᵒᵖ (TargetCorner H M) :=
  corner_finite_of_finite (targetCornerHom H) M (target_regular_finite H)

theorem triangular_finite_of_finite_corners (H : Subfield D) (M : Type*) [AddCommGroup M]
    [Module (TriangularRing H)ᵐᵒᵖ M]
    [FiniteDimensional Hᵐᵒᵖ (SourceCorner H M)]
    [FiniteDimensional Dᵐᵒᵖ (TargetCorner H M)] : Module.Finite (TriangularRing H)ᵐᵒᵖ M := by
  obtain ⟨s,hsfin,hs⟩ := Submodule.fg_def.mp (Module.Finite.fg_top (R := Hᵐᵒᵖ)
    (M := SourceCorner H M))
  obtain ⟨t,htfin,ht⟩ := Submodule.fg_def.mp (Module.Finite.fg_top (R := Dᵐᵒᵖ)
    (M := TargetCorner H M))
  let U : Set M := Subtype.val '' s ∪ Subtype.val '' t
  let V : Submodule (TriangularRing H)ᵐᵒᵖ M := Submodule.span (TriangularRing H)ᵐᵒᵖ U
  have hsrc (x : SourceCorner H M) : (x : M) ∈ V :=
    corner_coe_mem_of_span (sourceCornerHom H) M s hs V (fun y hy =>
      Submodule.subset_span (Set.mem_union_left _ ⟨y,hy,rfl⟩)) x
  have htgt (x : TargetCorner H M) : (x : M) ∈ V :=
    corner_coe_mem_of_span (targetCornerHom H) M t ht V (fun y hy =>
      Submodule.subset_span (Set.mem_union_right _ ⟨y,hy,rfl⟩)) x
  have hV : V = ⊤ := by
    apply Submodule.eq_top_iff'.mpr
    intro x
    have hx := V.add_mem (hsrc (cornerDecomposition H M x).1)
      (htgt (cornerDecomposition H M x).2)
    change (cornerDecomposition H M).symm (cornerDecomposition H M x) ∈ V at hx
    simpa only [AddEquiv.symm_apply_apply] using hx
  exact Module.Finite.of_fg_top (Submodule.fg_def.mpr
    ⟨U,(hsfin.image _).union (htfin.image _),hV⟩)

theorem triangular_finite_iff_corners (H : Subfield D) (M : Type*) [AddCommGroup M]
    [Module (TriangularRing H)ᵐᵒᵖ M] :
    Module.Finite (TriangularRing H)ᵐᵒᵖ M ↔
      FiniteDimensional Hᵐᵒᵖ (SourceCorner H M) ∧
      FiniteDimensional Dᵐᵒᵖ (TargetCorner H M) := by
  constructor
  · intro h
    letI := h
    exact ⟨source_corner_finite_of_finite H M,target_corner_finite_of_finite H M⟩
  · rintro ⟨hsrc,htgt⟩
    letI := hsrc
    letI := htgt
    exact triangular_finite_of_finite_corners H M

end

end QuantumFlags

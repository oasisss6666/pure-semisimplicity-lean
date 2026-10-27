import QuantumFlags.CornerFiniteness

namespace QuantumFlags

noncomputable section

variable {A : Type*} {B : Type*} {R : Type*} [Ring A] [Ring B] [Ring R]

def cornerSubmodule (f : A →ₙ+* R) (M : Type*) [AddCommGroup M] [Module R M]
    (V : Submodule R M) :
    letI := cornerFixedModule f M
    Submodule A (cornerFixedGroup f M) := by
  letI := cornerFixedModule f M
  exact {
    carrier := {x | (x : M) ∈ V}
    zero_mem' := V.zero_mem
    add_mem' := fun hx hy => V.add_mem hx hy
    smul_mem' := fun a x hx => V.smul_mem (f a) hx }

theorem two_corner_submodule_le_iff (f : A →ₙ+* R) (g : B →ₙ+* R) (h : f 1+g 1 = 1)
    (M : Type*) [AddCommGroup M] [Module R M] (V W : Submodule R M) :
    letI := cornerFixedModule f M
    letI := cornerFixedModule g M
    V ≤ W ↔ cornerSubmodule f M V ≤ cornerSubmodule f M W ∧
      cornerSubmodule g M V ≤ cornerSubmodule g M W := by
  letI := cornerFixedModule f M
  letI := cornerFixedModule g M
  constructor
  · intro hVW
    exact ⟨fun _ hx => hVW hx,fun _ hx => hVW hx⟩
  · rintro ⟨hf,hg⟩ x hx
    let xf : cornerFixedGroup f M := ⟨f 1 • x,corner_projection_idempotent f M x⟩
    let xg : cornerFixedGroup g M := ⟨g 1 • x,corner_projection_idempotent g M x⟩
    have hxf : (xf : M) ∈ W := hf (show xf ∈ cornerSubmodule f M V from V.smul_mem (f 1) hx)
    have hxg : (xg : M) ∈ W := hg (show xg ∈ cornerSubmodule g M V from V.smul_mem (g 1) hx)
    have hs : (xf : M)+(xg : M) = x := by
      change f 1 • x+g 1 • x = x
      rw [← add_smul,h,one_smul]
    rw [← hs]
    exact W.add_mem hxf hxg

def twoCornerSubmoduleEmbedding (f : A →ₙ+* R) (g : B →ₙ+* R) (h : f 1+g 1 = 1)
    (M : Type*) [AddCommGroup M] [Module R M] :
    letI := cornerFixedModule f M
    letI := cornerFixedModule g M
    Submodule R M ↪o (Submodule A (cornerFixedGroup f M) × Submodule B (cornerFixedGroup g M)) := by
  letI := cornerFixedModule f M
  letI := cornerFixedModule g M
  exact {
    toFun V := (cornerSubmodule f M V,cornerSubmodule g M V)
    inj' V W he := by
      apply le_antisymm
      · exact (two_corner_submodule_le_iff f g h M V W).mpr (le_of_eq he)
      · exact (two_corner_submodule_le_iff f g h M W V).mpr (le_of_eq he.symm)
    map_rel_iff' := by
      intro V W
      exact (two_corner_submodule_le_iff f g h M V W).symm }

theorem artinian_of_two_corners (f : A →ₙ+* R) (g : B →ₙ+* R) (h : f 1+g 1 = 1)
    (M : Type*) [AddCommGroup M] [Module R M]
    (hf : letI := cornerFixedModule f M; IsArtinian A (cornerFixedGroup f M))
    (hg : letI := cornerFixedModule g M; IsArtinian B (cornerFixedGroup g M)) :
    IsArtinian R M := by
  letI := cornerFixedModule f M
  letI := cornerFixedModule g M
  letI := hf
  letI := hg
  exact (twoCornerSubmoduleEmbedding f g h M).wellFoundedLT

theorem noetherian_of_two_corners (f : A →ₙ+* R) (g : B →ₙ+* R) (h : f 1+g 1 = 1)
    (M : Type*) [AddCommGroup M] [Module R M]
    (hf : letI := cornerFixedModule f M; IsNoetherian A (cornerFixedGroup f M))
    (hg : letI := cornerFixedModule g M; IsNoetherian B (cornerFixedGroup g M)) :
    IsNoetherian R M := by
  letI := cornerFixedModule f M
  letI := cornerFixedModule g M
  letI := hf
  letI := hg
  exact isNoetherian_iff.mpr (twoCornerSubmoduleEmbedding f g h M).dual.wellFoundedLT

end

end QuantumFlags

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Quotient.Basic

namespace QuantumFlags
noncomputable section
universe u v w
variable (K : Type u) [DivisionRing K]
variable {X : Type v} {Y : Type w} [AddCommGroup X] [Module K X]
  [AddCommGroup Y] [Module K Y]

def scalarLine (x : X) : K →ₗ[K] X where
  toFun a := a • x
  map_add' a b := add_smul a b x
  map_smul' a b := mul_smul a b x

theorem scalarLine_injective {x : X} (hx : x ≠ 0) : Function.Injective (scalarLine K x) :=
  smul_left_injective K hx

/-- A scalar line retract contained in the kernel, with both actual linear maps. -/
def HasKernelLine (f : X →ₗ[K] Y) : Prop :=
  ∃ (i : K →ₗ[K] X) (p : X →ₗ[K] K), p.comp i = LinearMap.id ∧ f.comp i = 0

/-- A scalar line retract detected by a projection annihilating the image. -/
def HasCokernelLine (f : X →ₗ[K] Y) : Prop :=
  ∃ (i : K →ₗ[K] Y) (p : Y →ₗ[K] K), p.comp i = LinearMap.id ∧ p.comp f = 0

theorem hasKernelLine_iff_not_injective (f : X →ₗ[K] Y) :
    HasKernelLine K f ↔ ¬ Function.Injective f := by
  constructor
  · rintro ⟨i,p,hpi,hfi⟩ hf
    have hi : i 1 = 0 := hf (by simpa using LinearMap.congr_fun hfi 1)
    have h := LinearMap.congr_fun hpi 1
    rw [LinearMap.comp_apply,hi,map_zero] at h
    exact zero_ne_one h
  · intro hf
    rw [Function.Injective] at hf
    push_neg at hf
    obtain ⟨x,y,hxy,hne⟩ := hf
    let z := x-y
    have hz : z ≠ 0 := sub_ne_zero.mpr hne
    have hfz : f z = 0 := by simp only [z,map_sub,hxy,sub_self]
    obtain ⟨p,hp⟩ := (scalarLine K z).exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr (scalarLine_injective K hz))
    refine ⟨scalarLine K z,p,hp,?_⟩
    apply LinearMap.ext
    intro a
    change f (a • z) = 0
    rw [map_smul,hfz,smul_zero]

theorem hasCokernelLine_iff_not_surjective (f : X →ₗ[K] Y) :
    HasCokernelLine K f ↔ ¬ Function.Surjective f := by
  constructor
  · rintro ⟨i,p,hpi,hpf⟩ hf
    obtain ⟨x,hx⟩ := hf (i 1)
    have h := LinearMap.congr_fun hpf x
    rw [LinearMap.comp_apply,hx] at h
    have he := LinearMap.congr_fun hpi 1
    change p (i 1) = 1 at he
    exact one_ne_zero (he.symm.trans h)
  · intro hf
    rw [Function.Surjective] at hf
    push_neg at hf
    obtain ⟨y,hy⟩ := hf
    let q := f.range.mkQ
    have hqy : q y ≠ 0 := by
      intro h
      obtain ⟨x,hx⟩ := (Submodule.Quotient.mk_eq_zero _).mp h
      exact hy x hx
    obtain ⟨l,hl⟩ := (scalarLine K (q y)).exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr (scalarLine_injective K hqy))
    refine ⟨scalarLine K y,l.comp q,?_,?_⟩
    · apply LinearMap.ext
      intro a
      change l (q (a • y)) = a
      rw [map_smul]
      exact LinearMap.congr_fun hl a
    · apply LinearMap.ext
      intro x
      change l (q (f x)) = 0
      have hq : q (f x) = 0 := (Submodule.Quotient.mk_eq_zero _).mpr ⟨x,rfl⟩
      rw [hq,map_zero]

end
end QuantumFlags

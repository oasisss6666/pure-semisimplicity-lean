import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic.Abel

namespace QuantumFlags
noncomputable section
variable {R : Type*} [Ring R] {A X : Type*}
  [AddCommGroup A] [Module R A] [AddCommGroup X] [Module R X]

def splitKernelProjection (i : A →ₗ[R] X) (p : X →ₗ[R] A)
    (hpi : p.comp i = LinearMap.id) : X →ₗ[R] p.ker where
  toFun x := ⟨x - i (p x), by
    change p (x - i (p x)) = 0
    rw [p.map_sub]
    have h := LinearMap.congr_fun hpi (p x)
    change p (i (p x)) = p x at h
    rw [h, sub_self]⟩
  map_add' x y := by
    apply Subtype.ext
    change (x+y) - i (p (x+y)) = (x-i (p x)) + (y-i (p y))
    rw [p.map_add, i.map_add]
    abel
  map_smul' a x := by
    apply Subtype.ext
    change a • x - i (p (a • x)) = a • (x-i (p x))
    rw [p.map_smul, i.map_smul, smul_sub]

theorem splitKernelProjection_comp_section (i : A →ₗ[R] X) (p : X →ₗ[R] A)
    (hpi : p.comp i = LinearMap.id) : (splitKernelProjection i p hpi).comp i = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change i x - i (p (i x)) = 0
  have h := LinearMap.congr_fun hpi x
  change p (i x) = x at h
  rw [h, sub_self]

theorem splitKernelProjection_comp_inclusion (i : A →ₗ[R] X) (p : X →ₗ[R] A)
    (hpi : p.comp i = LinearMap.id) :
    (splitKernelProjection i p hpi).comp p.ker.subtype = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (x : X) - i (p x) = x
  rw [x.property, map_zero, sub_zero]

theorem splitKernelProjection_total (i : A →ₗ[R] X) (p : X →ₗ[R] A)
    (hpi : p.comp i = LinearMap.id) :
    i.comp p + p.ker.subtype.comp (splitKernelProjection i p hpi) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  change i (p x) + (x-i (p x)) = x
  abel

end
end QuantumFlags

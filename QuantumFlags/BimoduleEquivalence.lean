import QuantumFlags.DivisionBimodules

namespace QuantumFlags

noncomputable section

universe u

structure BimoduleEquivalence (M N : DivisionBimodule.{u}) where
  left : M.LeftRing ≃+* N.LeftRing
  right : M.RightRing ≃+* N.RightRing
  space : M.Space ≃+ N.Space
  map_left : ∀ a x, space (a • x) = left a • space x
  map_right : ∀ a x, space (MulOpposite.op a • x) = MulOpposite.op (right a) • space x

namespace BimoduleEquivalence

variable {M N P : DivisionBimodule.{u}}

theorem symm_map_left (e : BimoduleEquivalence M N) (a : N.LeftRing) (x : N.Space) :
    e.space.symm (a • x) = e.left.symm a • e.space.symm x := by
  apply e.space.injective
  rw [e.space.apply_symm_apply, e.map_left, e.left.apply_symm_apply,
    e.space.apply_symm_apply]

theorem symm_map_right (e : BimoduleEquivalence M N) (a : N.RightRing) (x : N.Space) :
    e.space.symm (MulOpposite.op a • x) =
      MulOpposite.op (e.right.symm a) • e.space.symm x := by
  apply e.space.injective
  rw [e.space.apply_symm_apply, e.map_right, e.right.apply_symm_apply,
    e.space.apply_symm_apply]

def symm (e : BimoduleEquivalence M N) : BimoduleEquivalence N M where
  left := e.left.symm
  right := e.right.symm
  space := e.space.symm
  map_left := e.symm_map_left
  map_right := e.symm_map_right

def trans (e : BimoduleEquivalence M N) (f : BimoduleEquivalence N P) :
    BimoduleEquivalence M P where
  left := e.left.trans f.left
  right := e.right.trans f.right
  space := e.space.trans f.space
  map_left a x := by
    change f.space (e.space (a • x)) = f.left (e.left a) • f.space (e.space x)
    rw [e.map_left, f.map_left]
  map_right a x := by
    change f.space (e.space (MulOpposite.op a • x)) =
      MulOpposite.op (f.right (e.right a)) • f.space (e.space x)
    rw [e.map_right, f.map_right]

def transportDual (e : BimoduleEquivalence M N) (φ : RightDualSpace M) : RightDualSpace N where
  toFun y := e.right (φ (e.space.symm y))
  map_add' y z := by simp only [map_add]
  map_smul' r y := by
    change e.right (φ (e.space.symm (MulOpposite.op r.unop • y))) =
      e.right (φ (e.space.symm y))*r.unop
    rw [e.symm_map_right, map_smul]
    change e.right (φ (e.space.symm y)*e.right.symm r.unop) = _
    rw [map_mul, e.right.apply_symm_apply]

theorem transportDual_inverse (e : BimoduleEquivalence M N) (φ : RightDualSpace M) :
    e.symm.transportDual (e.transportDual φ) = φ := by
  apply LinearMap.ext
  intro x
  change e.right.symm (e.right (φ (e.space.symm (e.space x)))) = φ x
  rw [e.space.symm_apply_apply, e.right.symm_apply_apply]

def dual (e : BimoduleEquivalence M N) : BimoduleEquivalence (rightDual M) (rightDual N) where
  left := e.right
  right := e.left
  space := {
    toFun := e.transportDual
    invFun := e.symm.transportDual
    left_inv := e.transportDual_inverse
    right_inv φ := by
      apply LinearMap.ext
      intro y
      change e.right (e.right.symm (φ (e.space (e.space.symm y)))) = φ y
      rw [e.space.apply_symm_apply, e.right.apply_symm_apply]
    map_add' φ ψ := by
      apply LinearMap.ext
      intro y
      change e.right (φ (e.space.symm y)+ψ (e.space.symm y)) = _
      rw [map_add]
      rfl }
  map_left b φ := by
    apply LinearMap.ext
    intro y
    change e.right (b*φ (e.space.symm y)) = e.right b*e.right (φ (e.space.symm y))
    rw [map_mul]
  map_right a φ := by
    apply LinearMap.ext
    intro y
    change e.right (φ (a • e.space.symm y)) =
      e.right (φ (e.space.symm (e.left a • y)))
    rw [e.symm_map_left, e.left.symm_apply_apply]

theorem right_rank_eq (e : BimoduleEquivalence M N) :
    Module.rank M.RightRingᵐᵒᵖ M.Space = Module.rank N.RightRingᵐᵒᵖ N.Space := by
  apply rank_eq_of_equiv_equiv (RingEquiv.op e.right) e.space (RingEquiv.op e.right).bijective
  intro r x
  exact e.map_right r.unop x

theorem right_finrank_eq (e : BimoduleEquivalence M N) :
    Module.finrank M.RightRingᵐᵒᵖ M.Space = Module.finrank N.RightRingᵐᵒᵖ N.Space :=
  congrArg Cardinal.toNat e.right_rank_eq

end BimoduleEquivalence

end

end QuantumFlags

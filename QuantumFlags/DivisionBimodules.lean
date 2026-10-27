import QuantumFlags.RightDimensions

namespace QuantumFlags

noncomputable section

universe u

/-- Bimodules over possibly noncommutative division rings. -/
structure DivisionBimodule where
  LeftRing : Type u
  RightRing : Type u
  Space : Type u
  [leftDivision : DivisionRing LeftRing]
  [rightDivision : DivisionRing RightRing]
  [addGroup : AddCommGroup Space]
  [leftModule : Module LeftRing Space]
  [rightModule : Module RightRingᵐᵒᵖ Space]
  [commuting : SMulCommClass LeftRing RightRingᵐᵒᵖ Space]

attribute [instance] DivisionBimodule.leftDivision DivisionBimodule.rightDivision
  DivisionBimodule.addGroup DivisionBimodule.leftModule DivisionBimodule.rightModule
  DivisionBimodule.commuting

abbrev RightDualSpace (M : DivisionBimodule.{u}) :=
  M.Space →ₗ[M.RightRingᵐᵒᵖ] M.RightRing

def bimoduleLeftAction (M : DivisionBimodule.{u}) (a : M.LeftRing) :
    M.Space →ₗ[M.RightRingᵐᵒᵖ] M.Space where
  toFun x := a • x
  map_add' x y := smul_add a x y
  map_smul' r x := smul_comm a r x

@[instance_reducible]
def dualRightModule (M : DivisionBimodule.{u}) : Module M.LeftRingᵐᵒᵖ (RightDualSpace M) where
  smul a f := f.comp (bimoduleLeftAction M a.unop)
  one_smul f := by
    apply LinearMap.ext
    intro x
    change f ((1 : M.LeftRing) • x) = f x
    rw [one_smul]
  mul_smul a b f := by
    apply LinearMap.ext
    intro x
    change f ((b.unop*a.unop) • x) = f (b.unop • (a.unop • x))
    rw [mul_smul]
  smul_zero a := by
    apply LinearMap.ext
    intro x
    rfl
  smul_add a f g := by
    apply LinearMap.ext
    intro x
    rfl
  zero_smul f := by
    apply LinearMap.ext
    intro x
    change f ((0 : M.LeftRing) • x) = 0
    rw [zero_smul, map_zero]
  add_smul a b f := by
    apply LinearMap.ext
    intro x
    change f ((a.unop+b.unop) • x) = f (a.unop • x)+f (b.unop • x)
    rw [add_smul, map_add]

abbrev rightDual (M : DivisionBimodule.{u}) : DivisionBimodule.{u} := by
  letI := dualRightModule M
  exact {
    LeftRing := M.RightRing
    RightRing := M.LeftRing
    Space := RightDualSpace M
    commuting := ⟨fun a b f => by
      apply LinearMap.ext
      intro x
      rfl⟩ }

theorem rightDual_left_action (M : DivisionBimodule.{u}) (b : M.RightRing)
    (f : (rightDual M).Space) (x : M.Space) :
    (b • f) x = b*f x := rfl

def iteratedRightDual (M : DivisionBimodule.{u}) : ℕ → DivisionBimodule.{u}
  | 0 => M
  | n+1 => rightDual (iteratedRightDual M n)

variable {D : Type u} [DivisionRing D]

abbrev ambientBimodule (H : Subfield D) : DivisionBimodule.{u} where
  LeftRing := H
  RightRing := D
  Space := D
  commuting := ⟨fun a b x => (mul_assoc (a : D) x b.unop).symm⟩

end

end QuantumFlags

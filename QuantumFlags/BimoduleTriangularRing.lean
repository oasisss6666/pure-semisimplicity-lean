import QuantumFlags.TriangularCornerDecomposition
import QuantumFlags.DivisionBimodules
import Mathlib.Algebra.TrivSqZeroExt.Basic

namespace QuantumFlags

noncomputable section

universe u

@[instance_reducible]
def triangularCoefficientLeftModule (N : DivisionBimodule.{u}) :
    Module (N.LeftRing × N.RightRing) N.Space :=
  Module.compHom N.Space (RingHom.fst N.LeftRing N.RightRing)

@[instance_reducible]
def triangularCoefficientRightModule (N : DivisionBimodule.{u}) :
    Module (N.LeftRing × N.RightRing)ᵐᵒᵖ N.Space :=
  Module.compHom N.Space (RingHom.snd N.LeftRing N.RightRing).op

theorem triangularCoefficientComm (N : DivisionBimodule.{u}) :
    letI := triangularCoefficientLeftModule N
    letI := triangularCoefficientRightModule N
    SMulCommClass (N.LeftRing × N.RightRing) (N.LeftRing × N.RightRing)ᵐᵒᵖ N.Space := by
  letI := triangularCoefficientLeftModule N
  letI := triangularCoefficientRightModule N
  constructor
  intro a b n
  change a.1 • (MulOpposite.op b.unop.2 • n) = MulOpposite.op b.unop.2 • (a.1 • n)
  exact smul_comm a.1 (MulOpposite.op b.unop.2) n

/-- The triangular ring of an arbitrary division bimodule, as a square-zero extension. -/
def BimoduleTriangularRing (N : DivisionBimodule.{u}) : Type u :=
  TrivSqZeroExt (N.LeftRing × N.RightRing) N.Space

instance bimoduleTriangularRingRing (N : DivisionBimodule.{u}) : Ring (BimoduleTriangularRing N) := by
  letI := triangularCoefficientLeftModule N
  letI := triangularCoefficientRightModule N
  letI := triangularCoefficientComm N
  exact TrivSqZeroExt.ring

def bimoduleSourceHom (N : DivisionBimodule.{u}) : BimoduleTriangularRing N →+* N.LeftRing where
  toFun r := (TrivSqZeroExt.fst r).1
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

def bimoduleTargetHom (N : DivisionBimodule.{u}) : BimoduleTriangularRing N →+* N.RightRing where
  toFun r := (TrivSqZeroExt.fst r).2
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

def bimoduleCrossHom (N : DivisionBimodule.{u}) : BimoduleTriangularRing N →+ N.Space where
  toFun := TrivSqZeroExt.snd
  map_zero' := rfl
  map_add' _ _ := rfl

theorem bimodule_cross_mul (N : DivisionBimodule.{u}) (r s : BimoduleTriangularRing N) :
    bimoduleCrossHom N (r*s) = bimoduleSourceHom N r • bimoduleCrossHom N s+
      MulOpposite.op (bimoduleTargetHom N s) • bimoduleCrossHom N r := rfl

theorem bimodule_triangular_ext (N : DivisionBimodule.{u}) {r s : BimoduleTriangularRing N}
    (ha : bimoduleSourceHom N r = bimoduleSourceHom N s)
    (hb : bimoduleTargetHom N r = bimoduleTargetHom N s)
    (hn : bimoduleCrossHom N r = bimoduleCrossHom N s) : r = s :=
  Prod.ext (Prod.ext ha hb) hn

def bimoduleDiagonal (N : DivisionBimodule.{u}) (a : N.LeftRing) (b : N.RightRing) :
    BimoduleTriangularRing N := ((a,b),0)

def bimoduleOffDiagonal (N : DivisionBimodule.{u}) (n : N.Space) :
    BimoduleTriangularRing N := ((0,0),n)

@[simp] theorem bimodule_source_diagonal (N : DivisionBimodule.{u}) (a : N.LeftRing) (b : N.RightRing) :
    bimoduleSourceHom N (bimoduleDiagonal N a b) = a := rfl

@[simp] theorem bimodule_target_diagonal (N : DivisionBimodule.{u}) (a : N.LeftRing) (b : N.RightRing) :
    bimoduleTargetHom N (bimoduleDiagonal N a b) = b := rfl

@[simp] theorem bimodule_cross_diagonal (N : DivisionBimodule.{u}) (a : N.LeftRing) (b : N.RightRing) :
    bimoduleCrossHom N (bimoduleDiagonal N a b) = 0 := rfl

def bimoduleDiagonalRightHom (N : DivisionBimodule.{u}) :
    N.LeftRingᵐᵒᵖ × N.RightRingᵐᵒᵖ →+* (BimoduleTriangularRing N)ᵐᵒᵖ where
  toFun p := MulOpposite.op (bimoduleDiagonal N p.1.unop p.2.unop)
  map_one' := rfl
  map_zero' := rfl
  map_add' p q := by
    apply MulOpposite.unop_injective
    apply bimodule_triangular_ext N
    · rfl
    · rfl
    · change (0 : N.Space) = 0+0
      simp
  map_mul' p q := by
    apply MulOpposite.unop_injective
    apply bimodule_triangular_ext N
    · rfl
    · rfl
    · change (0 : N.Space) = q.1.unop • 0+MulOpposite.op p.2.unop • 0
      simp

def bimoduleSourceCornerHom (N : DivisionBimodule.{u}) :
    N.LeftRingᵐᵒᵖ →ₙ+* (BimoduleTriangularRing N)ᵐᵒᵖ :=
  (bimoduleDiagonalRightHom N).toNonUnitalRingHom.comp (productFirstCorner _ _)

def bimoduleTargetCornerHom (N : DivisionBimodule.{u}) :
    N.RightRingᵐᵒᵖ →ₙ+* (BimoduleTriangularRing N)ᵐᵒᵖ :=
  (bimoduleDiagonalRightHom N).toNonUnitalRingHom.comp (productSecondCorner _ _)

theorem bimodule_corner_units_sum (N : DivisionBimodule.{u}) :
    bimoduleSourceCornerHom N 1+bimoduleTargetCornerHom N 1 = 1 := by
  change bimoduleDiagonalRightHom N (1,0)+bimoduleDiagonalRightHom N (0,1) = 1
  have hp : ((1,0) : N.LeftRingᵐᵒᵖ × N.RightRingᵐᵒᵖ)+(0,1) = 1 := by ext <;> simp
  rw [← map_add,hp,map_one]

end

end QuantumFlags

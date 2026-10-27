import QuantumFlags.HomRepresentations
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Quotient.Basic

namespace QuantumFlags
noncomputable section
universe u v w

variable (N : DivisionBimodule.{u}) (X : Type v) [AddCommGroup X]
  [Module N.LeftRingᵐᵒᵖ X]

inductive BalancedRelationIndex where
  | zero (n : N.Space)
  | add (x y : X) (n : N.Space)
  | balance (a : N.LeftRing) (x : X) (n : N.Space)

def balancedRelation : BalancedRelationIndex N X → (X →₀ N.Space)
  | .zero n => Finsupp.single 0 n
  | .add x y n => Finsupp.single (x+y) n - Finsupp.single x n - Finsupp.single y n
  | .balance a x n => Finsupp.single (MulOpposite.op a • x) n - Finsupp.single x (a • n)

def balancedRelations : Submodule N.RightRingᵐᵒᵖ (X →₀ N.Space) :=
  Submodule.span N.RightRingᵐᵒᵖ (Set.range (balancedRelation N X))

abbrev BalancedTensor := (X →₀ N.Space) ⧸ balancedRelations N X

def tensorAt (x : X) : N.Space →ₗ[N.RightRingᵐᵒᵖ] BalancedTensor N X :=
  (balancedRelations N X).mkQ.comp (Finsupp.lsingle x)

def balancedPure (x : X) (n : N.Space) : BalancedTensor N X := tensorAt N X x n

theorem balancedRelation_mkQ_zero (i : BalancedRelationIndex N X) :
    (balancedRelations N X).mkQ (balancedRelation N X i) = 0 := by
  exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨i,rfl⟩)

theorem balancedPure_zero_left (n : N.Space) : balancedPure N X 0 n = 0 :=
  balancedRelation_mkQ_zero N X (.zero n)

theorem balancedPure_add_left (x y : X) (n : N.Space) :
    balancedPure N X (x+y) n = balancedPure N X x n + balancedPure N X y n := by
  have h := balancedRelation_mkQ_zero N X (.add x y n)
  change (balancedRelations N X).mkQ (_ - _ - _) = 0 at h
  rw [map_sub, map_sub, sub_sub, sub_eq_zero] at h
  exact h

theorem balancedPure_balance (a : N.LeftRing) (x : X) (n : N.Space) :
    balancedPure N X (MulOpposite.op a • x) n = balancedPure N X x (a • n) := by
  have h := balancedRelation_mkQ_zero N X (.balance a x n)
  change (balancedRelations N X).mkQ (_ - _) = 0 at h
  rw [map_sub, sub_eq_zero] at h
  exact h

theorem balancedPure_add_right (x : X) (m n : N.Space) :
    balancedPure N X x (m+n) = balancedPure N X x m + balancedPure N X x n :=
  (tensorAt N X x).map_add m n

theorem balancedPure_smul_right (x : X) (b : N.RightRingᵐᵒᵖ) (n : N.Space) :
    balancedPure N X x (b • n) = b • balancedPure N X x n :=
  (tensorAt N X x).map_smul b n

variable {Y : Type w} [AddCommGroup Y] [Module N.RightRingᵐᵒᵖ Y]

def balancedFreeLift
    (β : letI := rightHomModule N Y; X →ₗ[N.LeftRingᵐᵒᵖ] BimoduleRightHom N Y) :
    (X →₀ N.Space) →ₗ[N.RightRingᵐᵒᵖ] Y :=
  Finsupp.lsum ℤ (fun x => β x)

theorem balancedFreeLift_single
    (β : letI := rightHomModule N Y; X →ₗ[N.LeftRingᵐᵒᵖ] BimoduleRightHom N Y)
    (x : X) (n : N.Space) :
    balancedFreeLift N X β (Finsupp.single x n) = β x n :=
  Finsupp.lsum_single ℤ _ _ _

theorem balancedRelations_le_ker
    (β : letI := rightHomModule N Y; X →ₗ[N.LeftRingᵐᵒᵖ] BimoduleRightHom N Y) :
    balancedRelations N X ≤ LinearMap.ker (balancedFreeLift N X β) := by
  letI := rightHomModule N Y
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  change balancedFreeLift N X β (balancedRelation N X i) = 0
  cases i with
  | zero n => simp [balancedRelation, balancedFreeLift_single]
  | add x y n =>
    simp [balancedRelation, map_sub, balancedFreeLift_single, map_add]
  | balance a x n =>
    simp only [balancedRelation, map_sub, balancedFreeLift_single, map_smul]
    change β x (a • n) - β x (a • n) = 0
    exact sub_self _

def balancedTensorLift
    (β : letI := rightHomModule N Y; X →ₗ[N.LeftRingᵐᵒᵖ] BimoduleRightHom N Y) :
    BalancedTensor N X →ₗ[N.RightRingᵐᵒᵖ] Y :=
  (balancedRelations N X).liftQ (balancedFreeLift N X β) (balancedRelations_le_ker N X β)

theorem balancedTensorLift_pure
    (β : letI := rightHomModule N Y; X →ₗ[N.LeftRingᵐᵒᵖ] BimoduleRightHom N Y)
    (x : X) (n : N.Space) :
    balancedTensorLift N X β (balancedPure N X x n) = β x n :=
  balancedFreeLift_single N X β x n


def balancedTensorCurry (f : BalancedTensor N X →ₗ[N.RightRingᵐᵒᵖ] Y) :
    letI := rightHomModule N Y
    X →ₗ[N.LeftRingᵐᵒᵖ] BimoduleRightHom N Y := by
  letI := rightHomModule N Y
  exact {
    toFun x := f.comp (tensorAt N X x)
    map_add' x y := by
      apply LinearMap.ext
      intro n
      exact (congrArg f (balancedPure_add_left N X x y n)).trans (f.map_add _ _)
    map_smul' a x := by
      apply LinearMap.ext
      intro n
      change f (balancedPure N X (a • x) n) = f (balancedPure N X x (a.unop • n))
      rw [← MulOpposite.op_unop a]
      exact congrArg f (balancedPure_balance N X a.unop x n) }

theorem balancedTensorCurry_apply (f : BalancedTensor N X →ₗ[N.RightRingᵐᵒᵖ] Y)
    (x : X) (n : N.Space) :
    balancedTensorCurry N X f x n = f (balancedPure N X x n) := rfl

theorem balancedTensor_ext {f g : BalancedTensor N X →ₗ[N.RightRingᵐᵒᵖ] Y}
    (h : ∀ x n, f (balancedPure N X x n) = g (balancedPure N X x n)) : f = g := by
  apply Submodule.quot_hom_ext
  intro z
  have he : f.comp (balancedRelations N X).mkQ = g.comp (balancedRelations N X).mkQ := by
    apply Finsupp.lhom_ext
    exact h
  exact LinearMap.congr_fun he z

def balancedTensorHomEquiv :
    letI := rightHomModule N Y
    (BalancedTensor N X →ₗ[N.RightRingᵐᵒᵖ] Y) ≃
      (X →ₗ[N.LeftRingᵐᵒᵖ] BimoduleRightHom N Y) := by
  letI := rightHomModule N Y
  exact {
    toFun := balancedTensorCurry N X
    invFun := balancedTensorLift N X
    left_inv f := by
      apply balancedTensor_ext
      intro x n
      exact balancedTensorLift_pure N X _ x n
    right_inv β := by
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro n
      exact balancedTensorLift_pure N X β x n }


def balancedTensorMap {Z : Type*} [AddCommGroup Z] [Module N.LeftRingᵐᵒᵖ Z]
    (f : X →ₗ[N.LeftRingᵐᵒᵖ] Z) :
    BalancedTensor N X →ₗ[N.RightRingᵐᵒᵖ] BalancedTensor N Z := by
  letI := rightHomModule N (BalancedTensor N Z)
  exact balancedTensorLift N X ((balancedTensorCurry N Z LinearMap.id).comp f)

theorem balancedTensorMap_pure {Z : Type*} [AddCommGroup Z]
    [Module N.LeftRingᵐᵒᵖ Z] (f : X →ₗ[N.LeftRingᵐᵒᵖ] Z) (x : X) (n : N.Space) :
    balancedTensorMap N X f (balancedPure N X x n) = balancedPure N Z (f x) n :=
  balancedTensorLift_pure N X _ x n

theorem balancedTensorMap_identity :
    balancedTensorMap N X (LinearMap.id : X →ₗ[N.LeftRingᵐᵒᵖ] X) = LinearMap.id := by
  apply balancedTensor_ext
  intro x n
  exact balancedTensorMap_pure N X LinearMap.id x n

theorem balancedTensorMap_comp {Z W : Type*} [AddCommGroup Z]
    [Module N.LeftRingᵐᵒᵖ Z] [AddCommGroup W] [Module N.LeftRingᵐᵒᵖ W]
    (g : Z →ₗ[N.LeftRingᵐᵒᵖ] W) (f : X →ₗ[N.LeftRingᵐᵒᵖ] Z) :
    balancedTensorMap N X (g.comp f) =
      (balancedTensorMap N Z g).comp (balancedTensorMap N X f) := by
  apply balancedTensor_ext
  intro x n
  simp only [LinearMap.comp_apply, balancedTensorMap_pure]

end
end QuantumFlags

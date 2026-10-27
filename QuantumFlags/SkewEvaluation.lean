import QuantumFlags.SkewFractions
import Mathlib.Algebra.Group.Nat.Hom

namespace QuantumFlags

noncomputable section

variable {K L : Type*} [DivisionRing K] [MulSemiringAction (Multiplicative ℕ) K] [Semiring L]

theorem skew_polynomial_variable_relation (a : K) :
    (SkewPolynomial.X : SkewPolynomial K)*SkewPolynomial.C a =
      SkewPolynomial.C (SkewPolynomial.φ a)*SkewPolynomial.X := by
  rw [← SkewPolynomial.monomial_zero_left, SkewPolynomial.X_mul_monomial]
  rw [SkewPolynomial.C_mul_X_eq_monomial]

theorem skew_evaluation_power_relation (f : K →+* L) (v : L)
    (h : ∀ a, v*f a = f (SkewPolynomial.φ a)*v) (n : ℕ) (a : K) :
    v^n*f a = f ((SkewPolynomial.φ^[n]) a)*v^n := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_assoc, h, ← mul_assoc, ih]
    simp only [Function.iterate_succ_apply, mul_assoc, pow_succ]

def skewEvaluate (f : K →+* L) (v : L)
    (h : ∀ a, v*f a = f (SkewPolynomial.φ a)*v) : SkewPolynomial K →+* L :=
  SkewMonoidAlgebra.liftNCRingHom f (powersHom L v) (by
    intro a n
    change f (n • a)*v^n.toAdd = v^n.toAdd*f a
    have he : (SkewPolynomial.φ^[n.toAdd]) a = n • a :=
      SkewPolynomial.φ_iterate_apply n.toAdd a
    rw [← he]
    exact (skew_evaluation_power_relation f v h n.toAdd a).symm)

theorem skewEvaluate_monomial (f : K →+* L) (v : L)
    (h : ∀ a, v*f a = f (SkewPolynomial.φ a)*v) (n : ℕ) (a : K) :
    skewEvaluate f v h (SkewPolynomial.monomial n a) = f a*v^n := by
  simp [skewEvaluate, SkewPolynomial.monomial_def, SkewMonoidAlgebra.liftNCRingHom]

theorem skewEvaluate_C (f : K →+* L) (v : L)
    (h : ∀ a, v*f a = f (SkewPolynomial.φ a)*v) (a : K) :
    skewEvaluate f v h (SkewPolynomial.C a) = f a := by
  simpa only [SkewPolynomial.monomial_zero_left, pow_zero, mul_one] using
    skewEvaluate_monomial f v h 0 a

theorem skewEvaluate_X (f : K →+* L) (v : L)
    (h : ∀ a, v*f a = f (SkewPolynomial.φ a)*v) :
    skewEvaluate f v h SkewPolynomial.X = v := by
  simpa only [SkewPolynomial.X, map_one, pow_one, one_mul] using
    skewEvaluate_monomial f v h 1 1

theorem skew_ringHom_ext (f g : SkewPolynomial K →+* L)
    (hC : ∀ a, f (SkewPolynomial.C a) = g (SkewPolynomial.C a))
    (hX : f SkewPolynomial.X = g SkewPolynomial.X) : f = g := by
  apply RingHom.ext
  intro p
  induction p using SkewMonoidAlgebra.induction_on with
  | zero => simp
  | single n a =>
    change f (SkewPolynomial.monomial n.toAdd a) = g (SkewPolynomial.monomial n.toAdd a)
    rw [← SkewPolynomial.C_mul_X_pow_eq_monomial, map_mul, map_mul, map_pow, map_pow, hC, hX]
  | add p q hp hq => simp only [map_add, hp, hq]

def skewScaleHom (c : K) (hc : ∀ a : K, Commute c a) :
    SkewPolynomial K →+* SkewPolynomial K :=
  skewEvaluate SkewPolynomial.CRingHom (SkewPolynomial.C c*SkewPolynomial.X) (by
    intro a
    change (SkewPolynomial.C c*SkewPolynomial.X)*SkewPolynomial.C a =
      SkewPolynomial.C (SkewPolynomial.φ a)*(SkewPolynomial.C c*SkewPolynomial.X)
    rw [mul_assoc, skew_polynomial_variable_relation, ← mul_assoc,
      ← SkewPolynomial.C_mul, (hc (SkewPolynomial.φ a)).eq, SkewPolynomial.C_mul, mul_assoc])

theorem skewScaleHom_C (c : K) (hc : ∀ a : K, Commute c a) (a : K) :
    skewScaleHom c hc (SkewPolynomial.C a) = SkewPolynomial.C a :=
  skewEvaluate_C _ _ _ a

theorem skewScaleHom_X (c : K) (hc : ∀ a : K, Commute c a) :
    skewScaleHom c hc SkewPolynomial.X = SkewPolynomial.C c*SkewPolynomial.X :=
  skewEvaluate_X _ _ _

theorem skewScaleHom_inverse_left (c : K) (hc : ∀ a : K, Commute c a) (hcnz : c ≠ 0) :
    (skewScaleHom c⁻¹ (fun a => (hc a).inv_left₀)).comp (skewScaleHom c hc) =
      RingHom.id (SkewPolynomial K) := by
  apply skew_ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, skewScaleHom_C, RingHom.id_apply]
  · change skewScaleHom c⁻¹ (fun a => (hc a).inv_left₀)
      (skewScaleHom c hc SkewPolynomial.X) = SkewPolynomial.X
    rw [skewScaleHom_X, map_mul, skewScaleHom_C, skewScaleHom_X, ← mul_assoc,
      ← SkewPolynomial.C_mul, mul_inv_cancel₀ hcnz, SkewPolynomial.C_1, one_mul]

def skewScalingAut (c : K) (hc : ∀ a : K, Commute c a) (hcnz : c ≠ 0) :
    SkewPolynomial K ≃+* SkewPolynomial K where
  __ := skewScaleHom c hc
  invFun := skewScaleHom c⁻¹ (fun a => (hc a).inv_left₀)
  left_inv p := DFunLike.congr_fun (skewScaleHom_inverse_left c hc hcnz) p
  right_inv p := by
    change skewScaleHom c hc (skewScaleHom c⁻¹ (fun a => (hc a).inv_left₀) p) = p
    have he := skewScaleHom_inverse_left c⁻¹ (fun a => (hc a).inv_left₀) (inv_ne_zero hcnz)
    simpa only [inv_inv, RingHom.comp_apply, RingHom.id_apply] using DFunLike.congr_fun he p

theorem skewScalingAut_C (c : K) (hc : ∀ a : K, Commute c a) (hcnz : c ≠ 0) (a : K) :
    skewScalingAut c hc hcnz (SkewPolynomial.C a) = SkewPolynomial.C a :=
  skewScaleHom_C c hc a

theorem skewScalingAut_X (c : K) (hc : ∀ a : K, Commute c a) (hcnz : c ≠ 0) :
    skewScalingAut c hc hcnz SkewPolynomial.X = SkewPolynomial.C c*SkewPolynomial.X :=
  skewScaleHom_X c hc

end

end QuantumFlags

import Mathlib.Tactic.NoncommRing
import Mathlib.Algebra.Field.Rat

/-!
Ordered q-Pochhammer products and the two separate conjugation formulas
used in Section 4 of the manuscript. The ambient division ring is arbitrary.
Commutation hypotheses are stated explicitly, never inferred from a field model.
-/

namespace QuantumFlags

variable {D : Type*} [DivisionRing D]

def poch (q : D) : ℕ → D → D
  | 0, _ => 1
  | n+1, v => poch q n v * (1 - q^n * v)

@[simp] theorem poch_zero (q v : D) : poch q 0 v = 1 := rfl

theorem poch_succ (q v : D) (n : ℕ) :
    poch q (n+1) v = poch q n v * (1 - q^n * v) := rfl

/-- Elements commuting with q and v commute with every ordered product. -/
theorem commute_poch (q v z : D) (hzq : Commute z q) (hzv : Commute z v) (n : ℕ) :
    Commute z (poch q n v) := by
  induction n with
  | zero => exact Commute.one_right z
  | succ n ih =>
    exact ih.mul_right ((Commute.one_right z).sub_right ((hzq.pow_right n).mul_right hzv))

/-- Removing the first factor; this identity does not commute any factors. -/
theorem poch_prefix (q v : D) (n : ℕ) :
    poch q (n+1) v = (1-v) * poch q n (q*v) := by
  induction n with
  | zero => simp [poch]
  | succ n ih =>
    rw [poch_succ, ih, poch_succ]
    simp only [pow_succ, mul_assoc]

/-- A shift by q inverse gives the first quotient in (4.1). -/
theorem poch_inv_shift (q v : D) (hq : q ≠ 0) (n : ℕ) :
    poch q (n+1) (q⁻¹*v) = (1-q⁻¹*v) * poch q n v := by
  rw [poch_prefix]
  simp only [← mul_assoc, mul_inv_cancel₀ hq, one_mul]

theorem poch_right_quotient (q v : D) (n : ℕ) (hP : poch q n v ≠ 0) :
    (poch q n v)⁻¹ * poch q (n+1) v = 1-q^n*v := by
  rw [poch_succ, inv_mul_cancel_left₀ hP]

theorem poch_inverse_shift_quotient (q v : D) (hq : q ≠ 0)
    (hqv : Commute q v) (n : ℕ) (hP : poch q n v ≠ 0) :
    (poch q n v)⁻¹ * poch q (n+1) (q⁻¹*v) = 1-q⁻¹*v := by
  have hqP := commute_poch q v q (Commute.refl q) hqv n
  have hvP := commute_poch q v v hqv.symm (Commute.refl v) n
  have hfactor : Commute (1-q⁻¹*v) (poch q n v) :=
    (Commute.one_left _).sub_left (hqP.inv_left₀.mul_left hvP)
  rw [poch_inv_shift q v hq, hfactor.eq, inv_mul_cancel_left₀ hP]

theorem poch_left_quotient (q v : D) (hqv : Commute q v) (n : ℕ)
    (hQ : poch q n (q*v) ≠ 0) :
    (poch q n (q*v))⁻¹ * poch q (n+1) v = 1-v := by
  have hvQ := commute_poch q (q*v) v hqv.symm
    (hqv.symm.mul_right (Commute.refl v)) n
  have hfactor : Commute (1-v) (poch q n (q*v)) :=
    (Commute.one_left _).sub_left hvQ
  rw [poch_prefix, hfactor.eq, inv_mul_cancel_left₀ hQ]

/-- Intertwining an ordered product follows from the actual skew relation. -/
theorem poch_intertwine (q v x : D) (hxq : Commute x q)
    (hxv : x*v = (q⁻¹*v)*x) (n : ℕ) :
    x * poch q n v = poch q n (q⁻¹*v) * x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hf : x*(1-q^n*v) = (1-q^n*(q⁻¹*v))*x := by
      rw [mul_sub, mul_one, sub_mul, one_mul]
      congr 1
      calc
        x*(q^n*v) = (x*q^n)*v := (mul_assoc _ _ _).symm
        _ = (q^n*x)*v := by rw [(hxq.pow_right n).eq]
        _ = (q^n*(q⁻¹*v))*x := by
          rw [mul_assoc, hxv]
          simp only [mul_assoc]
    rw [poch_succ, poch_succ, ← mul_assoc, ih, mul_assoc, hf, ← mul_assoc]

/-- Section 4.3, with right coefficients a,b in the previous layer. -/
theorem right_strip_recursion (q v x a b : D) (hq : q ≠ 0)
    (hqv : Commute q v) (hxq : Commute x q)
    (hxv : x*v = (q⁻¹*v)*x)
    (haq : Commute a q) (hav : Commute a v)
    (hbq : Commute b q) (hbv : Commute b v)
    (p : ℕ) (hP : poch q p v ≠ 0) :
    (poch q p v)⁻¹ * (a+x*b) * poch q (p+1) v =
      (1-q^p*v)*a + (1-q⁻¹*v)*x*b := by
  have haP := (commute_poch q v a haq hav (p+1)).eq
  have hbP := (commute_poch q v b hbq hbv (p+1)).eq
  calc
    (poch q p v)⁻¹ * (a+x*b) * poch q (p+1) v =
        ((poch q p v)⁻¹ * poch q (p+1) v)*a +
        ((poch q p v)⁻¹ * poch q (p+1) (q⁻¹*v))*x*b := by
          simp only [mul_add, add_mul]
          congr 1
          · simp only [mul_assoc, haP]
          · calc
              ((poch q p v)⁻¹ * (x*b)) * poch q (p+1) v =
                  (poch q p v)⁻¹ * (x * (b * poch q (p+1) v)) := by simp [mul_assoc]
              _ = (poch q p v)⁻¹ * (x * (poch q (p+1) v * b)) := by rw [hbP]
              _ = ((poch q p v)⁻¹ * poch q (p+1) (q⁻¹*v))*x*b := by
                rw [← mul_assoc x, poch_intertwine q v x hxq hxv]
                simp only [mul_assoc]
    _ = (1-q^p*v)*a + (1-q⁻¹*v)*x*b := by
      rw [poch_right_quotient q v p hP,
        poch_inverse_shift_quotient q v hq hqv p hP]

/-- Section 4.4, proved separately with left coefficients a,b. -/
theorem left_strip_recursion (q v x a b : D) (hq : q ≠ 0)
    (hqv : Commute q v) (hxq : Commute x q)
    (hvx : v*x = x*(q*v))
    (haq : Commute a q) (hav : Commute a v)
    (hbq : Commute b q) (hbv : Commute b v)
    (p : ℕ) (hP : poch q p v ≠ 0) (hQ : poch q p (q*v) ≠ 0) :
    (poch q p v)⁻¹ * (a+b*x) * poch q (p+1) v =
      a*(1-q^p*v) + b*x*(1-v) := by
  have haP := (commute_poch q v a haq hav p).inv_right₀.eq
  have hbP := (commute_poch q v b hbq hbv p).inv_right₀.eq
  have hxv' : x*(q*v) = (q⁻¹*(q*v))*x := by
    simpa only [← mul_assoc, inv_mul_cancel₀ hq, one_mul] using hvx.symm
  have hPQ : poch q p v * x = x * poch q p (q*v) := by
    simpa only [← mul_assoc, inv_mul_cancel₀ hq, one_mul] using
      (poch_intertwine q (q*v) x hxq hxv' p).symm
  have hInv : (poch q p v)⁻¹*x = x*(poch q p (q*v))⁻¹ := by
    have h := congrArg (fun z => (poch q p v)⁻¹*z*(poch q p (q*v))⁻¹) hPQ
    simpa only [mul_assoc, inv_mul_cancel_left₀ hP, mul_inv_cancel₀ hQ, mul_one]
      using h.symm
  calc
    (poch q p v)⁻¹ * (a+b*x) * poch q (p+1) v =
        a*((poch q p v)⁻¹ * poch q (p+1) v) +
        b*x*((poch q p (q*v))⁻¹ * poch q (p+1) v) := by
      simp only [mul_add, add_mul]
      congr 1
      · simp only [mul_assoc, ← haP]
      · calc
          ((poch q p v)⁻¹ * (b*x)) * poch q (p+1) v =
              b*((poch q p v)⁻¹*x)*poch q (p+1) v := by
                simp only [← mul_assoc, ← hbP]
          _ = b*x*((poch q p (q*v))⁻¹ * poch q (p+1) v) := by
            rw [hInv]
            simp only [mul_assoc]
    _ = a*(1-q^p*v) + b*x*(1-v) := by
      rw [poch_right_quotient q v p hP, poch_left_quotient q v hqv p hQ]

end QuantumFlags

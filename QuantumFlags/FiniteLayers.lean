import QuantumFlags.BasisTransport

/-!
Finite-layer identities in Proposition 5.2 (prop:F) of the short manuscript.
The sequence is zero indexed: x 0 denotes the manuscript's t_1.
The ambient division ring is not assumed commutative.
-/

namespace QuantumFlags

variable {D : Type*} [DivisionRing D] [CharZero D]

def gamma (x : ℕ → D) (p : ℕ) : ℕ → D
  | 0 => 1 - x 0
  | n+1 => gamma x p n * poch (half D) p (x (n+1))

omit [CharZero D] in
theorem notRational_ne_zero {v : D} (hv : NotRational v) : v ≠ 0 := by
  simpa using hv 0

theorem gamma_ne_zero (x : ℕ → D) (hx : ∀ n, NotRational (x n)) (p n : ℕ) :
    gamma x p n ≠ 0 := by
  induction n with
  | zero => simpa [gamma] using linear_factor_ne_zero (x 0) (hx 0) 1
  | succ n ih => exact mul_ne_zero ih (poch_ne_zero _ (hx (n+1)) (1/2) p)

omit [CharZero D] in
theorem matrix_mul_entries_commute (A B : Mat2 D) (z : D)
    (hA : ∀ i j, Commute (A i j) z) (hB : ∀ i j, Commute (B i j) z) :
    ∀ i j, Commute ((A*B) i j) z := by
  intro i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  exact ((hA i 0).mul_left (hB 0 j)).add_left ((hA i 1).mul_left (hB 1 j))

theorem rat_matrix_entries_commute (A : Mat2 ℚ) (z : D) :
    ∀ i j, Commute (liftRat A i j) z := by
  intro i j
  exact Rat.cast_commute (A i j) z

omit [CharZero D] in
theorem diag_entries_commute (v z : D) (h : Commute v z) :
    ∀ i j, Commute (diagUnit v i j) z := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [diagUnit, h, Commute.one_left, Commute.zero_left]

theorem rightRecursion_entries_commute (p : ℕ) (x : ℕ → D) (n : ℕ) (z : D)
    (hz : ∀ k, k < n → Commute (x k) z) :
    ∀ i j, Commute (rightRecursion p x n i j) z := by
  induction n with
  | zero =>
    intro i j
    fin_cases i <;> fin_cases j <;> simp [rightRecursion, Commute.one_left, Commute.zero_left]
  | succ n ih =>
    apply matrix_mul_entries_commute
    · exact matrix_mul_entries_commute _ _ _ (rat_matrix_entries_commute _ z)
        (diag_entries_commute _ _ (hz n (Nat.lt_succ_self n)))
    · exact ih (fun k hk => hz k (Nat.lt_succ_of_lt hk))

theorem leftRecursion_entries_commute (p : ℕ) (x : ℕ → D) (n : ℕ) (z : D)
    (hz : ∀ k, k < n → Commute (x k) z) :
    ∀ i j, Commute (leftRecursion p x n i j) z := by
  induction n with
  | zero =>
    intro i j
    fin_cases i <;> fin_cases j <;> simp [leftRecursion, Commute.one_left, Commute.zero_left]
  | succ n ih =>
    apply matrix_mul_entries_commute
    · exact matrix_mul_entries_commute _ _ _
        (ih (fun k hk => hz k (Nat.lt_succ_of_lt hk)))
        (diag_entries_commute _ _ (hz n (Nat.lt_succ_self n)))
    · exact rat_matrix_entries_commute _ z

def conjugatePair (x : ℕ → D) (p n : ℕ) (i : Fin 2) : D :=
  (gamma x p n)⁻¹ * (x 0)^i.val * gamma x (p+1) n

theorem conjugatePair_zero (x : ℕ → D) (hx : NotRational (x 0))
    (p : ℕ) (i : Fin 2) : conjugatePair x p 0 i = (x 0)^i.val := by
  have hg : 1 - x 0 ≠ 0 := by simpa using linear_factor_ne_zero (x 0) hx 1
  have hc : Commute (1-x 0) ((x 0)^i.val) :=
    (Commute.one_left _).sub_left (Commute.refl _)
      |>.pow_right i.val
  simp only [conjugatePair, gamma]
  rw [hc.inv_left₀.eq, mul_assoc, inv_mul_cancel₀ hg, mul_one]

omit [CharZero D] in
theorem conjugatePair_succ (x : ℕ → D) (p n : ℕ) (i : Fin 2) :
    conjugatePair x p (n+1) i =
      (poch (half D) p (x (n+1)))⁻¹ * conjugatePair x p n i *
        poch (half D) (p+1) (x (n+1)) := by
  simp only [conjugatePair, gamma, mul_inv_rev]
  simp only [mul_assoc]

/-- The recursively constructed right coordinate matrix represents the exact
Gamma-conjugated elements, at every finite layer. -/
theorem right_finite_layer_coordinates (x : ℕ → D)
    (hx : ∀ n, NotRational (x n))
    (hadj : ∀ n, x (n+1)*x n = half D*x n*x (n+1))
    (hfar : ∀ i j, i+1 < j → Commute (x i) (x j)) (p n : ℕ) (i : Fin 2) :
    rightCoordinate (x n) (rightRecursion p x n) i = conjugatePair x p n i := by
  induction n with
  | zero =>
    rw [conjugatePair_zero x (hx 0)]
    fin_cases i <;> simp [rightCoordinate, rightRecursion, Matrix.one_apply]
  | succ n ih =>
    rw [rightRecursion, right_local_flag_step _ _ (hx (n+1)) (hadj n)]
    · rw [ih, conjugatePair_succ]
    · exact rightRecursion_entries_commute p x n _
        (fun k hk => hfar k (n+1) (Nat.succ_lt_succ hk)) 0 i
    · exact rightRecursion_entries_commute p x n _
        (fun k hk => hfar k (n+1) (Nat.succ_lt_succ hk)) 1 i

/-- The separately ordered left coordinate matrix represents those same elements. -/
theorem left_finite_layer_coordinates (x : ℕ → D)
    (hx : ∀ n, NotRational (x n))
    (hadj : ∀ n, x (n+1)*x n = half D*x n*x (n+1))
    (hfar : ∀ i j, i+1 < j → Commute (x i) (x j)) (p n : ℕ) (i : Fin 2) :
    leftCoordinate (leftRecursion p x n) (x n) i = conjugatePair x p n i := by
  induction n with
  | zero =>
    rw [conjugatePair_zero x (hx 0)]
    fin_cases i <;> simp [leftCoordinate, leftRecursion, Matrix.one_apply]
  | succ n ih =>
    rw [leftRecursion, left_local_flag_step _ _ (hx (n+1)) (hadj n)]
    · rw [ih, conjugatePair_succ]
    · exact leftRecursion_entries_commute p x n _
        (fun k hk => hfar k (n+1) (Nat.succ_lt_succ hk)) i 0
    · exact leftRecursion_entries_commute p x n _
        (fun k hk => hfar k (n+1) (Nat.succ_lt_succ hk)) i 1

end QuantumFlags

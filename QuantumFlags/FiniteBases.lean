import QuantumFlags.FiniteLayers
import Mathlib.Algebra.Field.Subfield.Basic

namespace QuantumFlags

variable {K D : Type*} [DivisionRing K] [DivisionRing D] [CharZero K] [CharZero D]

theorem liftRat_map (ι : K →+* D) (A : Mat2 ℚ) :
    (liftRat (D := K) A).map ι = liftRat (D := D) A := by
  ext i j
  simp [liftRat, Rat.castHom, map_ratCast]

omit [CharZero K] [CharZero D] in
theorem diagUnit_map (ι : K →+* D) (a : K) :
    (diagUnit a).map ι = diagUnit (ι a) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagUnit]

theorem rightRecursion_map (ι : K →+* D) (p : ℕ) (y : ℕ → K) (n : ℕ) :
    (rightRecursion p y n).map ι = rightRecursion p (fun k => ι (y k)) n := by
  induction n with
  | zero => exact Matrix.map_one _ (map_zero _) (map_one _)
  | succ n ih =>
    simp only [rightRecursion, Matrix.map_mul, ih, rightStep, liftRat_map, diagUnit_map]

theorem leftRecursion_map (ι : K →+* D) (p : ℕ) (y : ℕ → K) (n : ℕ) :
    (leftRecursion p y n).map ι = leftRecursion p (fun k => ι (y k)) n := by
  induction n with
  | zero => exact Matrix.map_one _ (map_zero _) (map_one _)
  | succ n ih =>
    simp only [leftRecursion, Matrix.map_mul, ih, leftStep, liftRat_map, diagUnit_map]

theorem rightRecursion_congr_prefix (p : ℕ) (x y : ℕ → D) (n : ℕ)
    (h : ∀ k, k < n → x k = y k) : rightRecursion p x n = rightRecursion p y n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rightRecursion, h n (Nat.lt_succ_self n),
      ih (fun k hk => h k (Nat.lt_succ_of_lt hk))]

theorem leftRecursion_congr_prefix (p : ℕ) (x y : ℕ → D) (n : ℕ)
    (h : ∀ k, k < n → x k = y k) : leftRecursion p x n = leftRecursion p y n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [leftRecursion, h n (Nat.lt_succ_self n),
      ih (fun k hk => h k (Nat.lt_succ_of_lt hk))]

def rightPairEval (ι : K →+* D) (w : Fin 2 → D) (c : Fin 2 → K) : D :=
  w 0 * ι (c 0) + w 1 * ι (c 1)

def leftPairEval (ι : K →+* D) (w : Fin 2 → D) (c : Fin 2 → K) : D :=
  ι (c 0) * w 0 + ι (c 1) * w 1

theorem right_finite_layer_basis (ι : K →+* D) (x : ℕ → D)
    (hx : ∀ n, NotRational (x n))
    (hadj : ∀ n, x (n+1)*x n = half D*x n*x (n+1))
    (hfar : ∀ i j, i+1 < j → Commute (x i) (x j))
    (p n : ℕ) (hp : 1 ≤ p) (y : ℕ → K) (hy : ∀ k, y k ≠ 0)
    (hxy : ∀ k, k < n → ι (y k) = x k)
    (hbase : Function.Injective (rightEval ι (x n))) :
    Function.Injective (rightPairEval ι (conjugatePair x p n)) ∧
      Set.range (rightPairEval ι (conjugatePair x p n)) =
        Set.range (rightEval ι (x n)) := by
  have hc (i : Fin 2) :
      ι (rightRecursion p y n 0 i) + x n * ι (rightRecursion p y n 1 i) =
        conjugatePair x p n i := by
    change rightCoordinate (x n) ((rightRecursion p y n).map ι) i = _
    rw [rightRecursion_map, rightRecursion_congr_prefix p _ x n hxy]
    exact right_finite_layer_coordinates x hx hadj hfar p n i
  have heq : rightFamilyEval ι (x n) (rightRecursion p y n) =
      rightPairEval ι (conjugatePair x p n) := by
    funext c
    simp only [rightFamilyEval, rightPairEval, hc]
  rw [← heq]
  exact right_recursion_basis ι _ hbase p hp y hy n

theorem left_finite_layer_basis (ι : K →+* D) (x : ℕ → D)
    (hx : ∀ n, NotRational (x n))
    (hadj : ∀ n, x (n+1)*x n = half D*x n*x (n+1))
    (hfar : ∀ i j, i+1 < j → Commute (x i) (x j))
    (p n : ℕ) (hp : 1 ≤ p) (y : ℕ → K) (hy : ∀ k, y k ≠ 0)
    (hxy : ∀ k, k < n → ι (y k) = x k)
    (hbase : Function.Injective (leftEval ι (x n))) :
    Function.Injective (leftPairEval ι (conjugatePair x p n)) ∧
      Set.range (leftPairEval ι (conjugatePair x p n)) =
        Set.range (leftEval ι (x n)) := by
  have hc (i : Fin 2) :
      ι (leftRecursion p y n i 0) + ι (leftRecursion p y n i 1)*x n =
        conjugatePair x p n i := by
    change leftCoordinate ((leftRecursion p y n).map ι) (x n) i = _
    rw [leftRecursion_map, leftRecursion_congr_prefix p _ x n hxy]
    exact left_finite_layer_coordinates x hx hadj hfar p n i
  have heq : leftFamilyEval ι (x n) (leftRecursion p y n) =
      leftPairEval ι (conjugatePair x p n) := by
    funext c
    simp only [leftFamilyEval, leftPairEval, hc]
  rw [← heq]
  exact left_recursion_basis ι _ hbase p hp y hy n

omit [CharZero K] [CharZero D] in
/-- Normalization by the new generator identifies the left and right PBW strips. -/
theorem normalizing_pair_ranges (ι : K →+* D) (v : D) (τ : K ≃+* K)
    (hτ : ∀ a, v*ι a = ι (τ a)*v) :
    Set.range (rightEval ι v) = Set.range (leftEval ι v) := by
  ext z
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨![c 0, τ (c 1)], ?_⟩
    simp [rightEval, leftEval, hτ]
  · rintro ⟨c, rfl⟩
    refine ⟨![c 0, τ.symm (c 1)], ?_⟩
    simp [rightEval, leftEval, hτ]

def leftConjugatedStrip (ι : K →+* D) (t g : D) (c : Fin 2 → K) : D :=
  g*ι (c 0)*g⁻¹ + g*ι (c 1)*g⁻¹*t

def rightConjugatedStrip (ι : K →+* D) (t g : D) (c : Fin 2 → K) : D :=
  g*ι (c 0)*g⁻¹ + t*(g*ι (c 1)*g⁻¹)

omit [CharZero K] [CharZero D] in
theorem left_strip_transform (ι : K →+* D) (t g h : D) (hg : g ≠ 0)
    (c : Fin 2 → K) :
    g⁻¹ * leftConjugatedStrip ι t g c * h =
      leftPairEval ι ![g⁻¹*h, g⁻¹*t*h] c := by
  simp only [leftConjugatedStrip, leftPairEval, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_add, add_mul, mul_assoc,
    inv_mul_cancel_left₀ hg]

omit [CharZero K] [CharZero D] in
theorem right_strip_transform (ι : K →+* D) (t g h : D) (hh : h ≠ 0)
    (c : Fin 2 → K) :
    g⁻¹ * rightConjugatedStrip ι t h c * h =
      rightPairEval ι ![g⁻¹*h, g⁻¹*t*h] c := by
  simp only [rightConjugatedStrip, rightPairEval, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_add, add_mul, mul_assoc,
    inv_mul_cancel₀ hh, mul_one]

omit [CharZero K] [CharZero D] in
theorem sandwich_injective (g h : D) (hg : g ≠ 0) (hh : h ≠ 0) :
    Function.Injective (fun z => g⁻¹*z*h) := by
  intro a b hab
  exact (mul_left_cancel₀ (inv_ne_zero hg)) (mul_right_cancel₀ hh hab)

omit [CharZero D] in
theorem conjugatePair_eq_vector (x : ℕ → D) (p n : ℕ) :
    conjugatePair x p n =
      ![(gamma x p n)⁻¹*gamma x (p+1) n,
        (gamma x p n)⁻¹*x 0*gamma x (p+1) n] := by
  funext i
  fin_cases i <;> simp [conjugatePair]

/-- The local adjacent-flag equality, including directness on both sides.
Only PBW independence, the normalizing automorphism, the quantum relations,
and membership of the earlier generators in the coefficient ring are assumed. -/
theorem finite_adjacent_flags (ι : K →+* D) (x : ℕ → D)
    (hx : ∀ n, NotRational (x n))
    (hadj : ∀ n, x (n+1)*x n = half D*x n*x (n+1))
    (hfar : ∀ i j, i+1 < j → Commute (x i) (x j))
    (p n : ℕ) (hp : 1 ≤ p) (y : ℕ → K) (hy : ∀ k, y k ≠ 0)
    (hxy : ∀ k, k < n → ι (y k) = x k)
    (hr : Function.Injective (rightEval ι (x n)))
    (hl : Function.Injective (leftEval ι (x n)))
    (τ : K ≃+* K) (hτ : ∀ a, x n*ι a = ι (τ a)*x n) :
    Function.Injective (leftConjugatedStrip ι (x 0) (gamma x p n)) ∧
    Function.Injective (rightConjugatedStrip ι (x 0) (gamma x (p+1) n)) ∧
    Set.range (leftConjugatedStrip ι (x 0) (gamma x p n)) =
      Set.range (rightConjugatedStrip ι (x 0) (gamma x (p+1) n)) := by
  obtain ⟨hri, hrr⟩ := right_finite_layer_basis ι x hx hadj hfar p n hp y hy hxy hr
  obtain ⟨hli, hlr⟩ := left_finite_layer_basis ι x hx hadj hfar p n hp y hy hxy hl
  have hpair := (hlr.trans (normalizing_pair_ranges ι _ τ hτ).symm).trans hrr.symm
  have hg := gamma_ne_zero x hx p n
  have hh := gamma_ne_zero x hx (p+1) n
  have hL (c : Fin 2 → K) :
      (gamma x p n)⁻¹ * leftConjugatedStrip ι (x 0) (gamma x p n) c *
          gamma x (p+1) n = leftPairEval ι (conjugatePair x p n) c := by
    rw [conjugatePair_eq_vector]
    exact left_strip_transform ι _ _ _ hg c
  have hR (c : Fin 2 → K) :
      (gamma x p n)⁻¹ * rightConjugatedStrip ι (x 0) (gamma x (p+1) n) c *
          gamma x (p+1) n = rightPairEval ι (conjugatePair x p n) c := by
    rw [conjugatePair_eq_vector]
    exact right_strip_transform ι _ _ _ hh c
  refine ⟨?_, ?_, ?_⟩
  · intro c d h
    apply hli
    rw [← hL, ← hL, h]
  · intro c d h
    apply hri
    rw [← hR, ← hR, h]
  · ext z
    constructor
    · rintro ⟨c, rfl⟩
      have hm : leftPairEval ι (conjugatePair x p n) c ∈
          Set.range (rightPairEval ι (conjugatePair x p n)) :=
        hpair ▸ Set.mem_range_self c
      obtain ⟨d, hd⟩ := hm
      refine ⟨d, ?_⟩
      apply sandwich_injective _ _ hg hh
      dsimp only
      rw [hR, hL, hd]
    · rintro ⟨c, rfl⟩
      have hm : rightPairEval ι (conjugatePair x p n) c ∈
          Set.range (leftPairEval ι (conjugatePair x p n)) :=
        hpair.symm ▸ Set.mem_range_self c
      obtain ⟨d, hd⟩ := hm
      refine ⟨d, ?_⟩
      apply sandwich_injective _ _ hg hh
      dsimp only
      rw [hL, hR, hd]

end QuantumFlags

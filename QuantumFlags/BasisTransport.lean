import QuantumFlags.Coordinates

/-!
The coefficient division ring K and the ambient division ring D are distinct.
This file closes the basis-transport step for a noncentral ring embedding.
The PBW hypothesis for the original pair (1,v) is explicit.
-/

namespace QuantumFlags

open Matrix

variable {K D : Type*} [DivisionRing K] [DivisionRing D]

def rightEval (ι : K →+* D) (v : D) (c : Fin 2 → K) : D :=
  ι (c 0) + v * ι (c 1)

def rightFamilyEval (ι : K →+* D) (v : D) (M : Mat2 K) (c : Fin 2 → K) : D :=
  (ι (M 0 0) + v * ι (M 1 0)) * ι (c 0) +
  (ι (M 0 1) + v * ι (M 1 1)) * ι (c 1)

theorem right_change_coordinates (ι : K →+* D) (v : D) (M : Mat2 K)
    (c : Fin 2 → K) :
    rightFamilyEval ι v M c = rightEval ι v (M.mulVec c) := by
  simp [rightFamilyEval, rightEval, mulVec, dotProduct, Fin.sum_univ_two]
  noncomm_ring

/-- Injectivity is exactly right linear independence of the new pair;
range equality is exactly equality of the two right spans. -/
theorem right_basis_transport (ι : K →+* D) (v : D)
    (hbase : Function.Injective (rightEval ι v))
    (M : Mat2 K) (hM : HasInverse M) :
    Function.Injective (rightFamilyEval ι v M) ∧
    Set.range (rightFamilyEval ι v M) = Set.range (rightEval ι v) := by
  constructor
  · intro c d h
    apply hM.mulVec_bijective.injective
    apply hbase
    simpa only [right_change_coordinates] using h
  · ext z
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨M.mulVec c, (right_change_coordinates ι v M c).symm⟩
    · rintro ⟨c, rfl⟩
      obtain ⟨d, hd⟩ := hM.mulVec_bijective.surjective c
      exact ⟨d, by rw [right_change_coordinates, hd]⟩

def leftEval (ι : K →+* D) (v : D) (c : Fin 2 → K) : D :=
  ι (c 0) + ι (c 1) * v

def leftFamilyEval (ι : K →+* D) (v : D) (M : Mat2 K) (c : Fin 2 → K) : D :=
  ι (c 0) * (ι (M 0 0) + ι (M 0 1) * v) +
  ι (c 1) * (ι (M 1 0) + ι (M 1 1) * v)

theorem left_change_coordinates (ι : K →+* D) (v : D) (M : Mat2 K)
    (c : Fin 2 → K) :
    leftFamilyEval ι v M c = leftEval ι v (vecMul c M) := by
  simp [leftFamilyEval, leftEval, vecMul, dotProduct, Fin.sum_univ_two]
  noncomm_ring

/-- The analogous left-basis statement, proved in its own coefficient order. -/
theorem left_basis_transport (ι : K →+* D) (v : D)
    (hbase : Function.Injective (leftEval ι v))
    (M : Mat2 K) (hM : HasInverse M) :
    Function.Injective (leftFamilyEval ι v M) ∧
    Set.range (leftFamilyEval ι v M) = Set.range (leftEval ι v) := by
  constructor
  · intro c d h
    apply hM.vecMul_bijective.injective
    apply hbase
    simpa only [left_change_coordinates] using h
  · ext z
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨vecMul c M, (left_change_coordinates ι v M c).symm⟩
    · rintro ⟨c, rfl⟩
      obtain ⟨d, hd⟩ := hM.vecMul_bijective.surjective c
      change vecMul d M = c at hd
      exact ⟨d, by rw [left_change_coordinates, hd]⟩

variable [CharZero K]

theorem right_recursion_basis (ι : K →+* D) (v : D)
    (hbase : Function.Injective (rightEval ι v))
    (p : ℕ) (hp : 1 ≤ p) (x : ℕ → K) (hx : ∀ n, x n ≠ 0) (n : ℕ) :
    Function.Injective (rightFamilyEval ι v (rightRecursion p x n)) ∧
    Set.range (rightFamilyEval ι v (rightRecursion p x n)) =
      Set.range (rightEval ι v) := by
  exact right_basis_transport ι v hbase _ (rightRecursion_hasInverse p hp x hx n)

theorem left_recursion_basis (ι : K →+* D) (v : D)
    (hbase : Function.Injective (leftEval ι v))
    (p : ℕ) (hp : 1 ≤ p) (x : ℕ → K) (hx : ∀ n, x n ≠ 0) (n : ℕ) :
    Function.Injective (leftFamilyEval ι v (leftRecursion p x n)) ∧
    Set.range (leftFamilyEval ι v (leftRecursion p x n)) =
      Set.range (leftEval ι v) := by
  exact left_basis_transport ι v hbase _ (leftRecursion_hasInverse p hp x hx n)

end QuantumFlags

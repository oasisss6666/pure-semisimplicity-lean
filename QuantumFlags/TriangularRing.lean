import QuantumFlags.LeftTails

namespace QuantumFlags

noncomputable section

variable {D : Type*} [DivisionRing D]

def triangularSubring (H : Subfield D) : Subring (Matrix (Fin 2) (Fin 2) D) where
  carrier M := M 1 0 = 0 ∧ M 0 0 ∈ H
  zero_mem' := by
    change (0 : Matrix (Fin 2) (Fin 2) D) 1 0 = 0 ∧
      (0 : Matrix (Fin 2) (Fin 2) D) 0 0 ∈ H
    exact ⟨rfl,H.zero_mem⟩
  one_mem' := by
    change (1 : Matrix (Fin 2) (Fin 2) D) 1 0 = 0 ∧
      (1 : Matrix (Fin 2) (Fin 2) D) 0 0 ∈ H
    constructor
    · simp
    · simpa using H.one_mem
  add_mem' := by
    intro M N hM hN
    exact ⟨by simp [hM.1,hN.1], H.add_mem hM.2 hN.2⟩
  neg_mem' := by
    intro M hM
    exact ⟨by simp [hM.1], H.neg_mem hM.2⟩
  mul_mem' := by
    intro M N hM hN
    constructor
    · simp [Matrix.mul_apply, Fin.sum_univ_two, hM.1, hN.1]
    · simpa [Matrix.mul_apply, Fin.sum_univ_two, hN.1] using H.mul_mem hM.2 hN.2

abbrev TriangularRing (H : Subfield D) := triangularSubring H

def offDiagonal (H : Subfield D) (x : D) : TriangularRing H :=
  ⟨!![0,x;0,0], by
    change (!![0,x;0,0] : Matrix (Fin 2) (Fin 2) D) 1 0 = 0 ∧
      (!![0,x;0,0] : Matrix (Fin 2) (Fin 2) D) 0 0 ∈ H
    simpa using H.zero_mem⟩

def cornerLeftIdeal (H : Subfield D) (V : Submodule H D) : Ideal (TriangularRing H) where
  carrier M := (M : Matrix (Fin 2) (Fin 2) D) 0 0 = 0 ∧
    (M : Matrix (Fin 2) (Fin 2) D) 1 1 = 0 ∧
    (M : Matrix (Fin 2) (Fin 2) D) 0 1 ∈ V
  zero_mem' := by
    change (0 : Matrix (Fin 2) (Fin 2) D) 0 0 = 0 ∧
      (0 : Matrix (Fin 2) (Fin 2) D) 1 1 = 0 ∧
      (0 : Matrix (Fin 2) (Fin 2) D) 0 1 ∈ V
    exact ⟨rfl,rfl,V.zero_mem⟩
  add_mem' := by
    intro M N hM hN
    exact ⟨by simpa only [Subring.coe_add, Matrix.add_apply,hM.1,hN.1] using add_zero (0 : D),
      by simpa only [Subring.coe_add,Matrix.add_apply,hM.2.1,hN.2.1] using add_zero (0 : D),
      V.add_mem hM.2.2 hN.2.2⟩
  smul_mem' := by
    intro A M hM
    change ((A : Matrix (Fin 2) (Fin 2) D)*(M : Matrix (Fin 2) (Fin 2) D)) 0 0 = 0 ∧
      ((A : Matrix (Fin 2) (Fin 2) D)*(M : Matrix (Fin 2) (Fin 2) D)) 1 1 = 0 ∧
      ((A : Matrix (Fin 2) (Fin 2) D)*(M : Matrix (Fin 2) (Fin 2) D)) 0 1 ∈ V
    constructor
    · simp [Matrix.mul_apply,Fin.sum_univ_two,hM.1,M.property.1]
    constructor
    · simp [Matrix.mul_apply,Fin.sum_univ_two,A.property.1,hM.2.1]
    · have hm := V.smul_mem
        (⟨(A : Matrix (Fin 2) (Fin 2) D) 0 0,A.property.2⟩ : H) hM.2.2
      simpa [Matrix.mul_apply,Fin.sum_univ_two,hM.2.1,Subfield.smul_def] using hm

theorem offDiagonal_mem_cornerLeftIdeal (H : Subfield D) (V : Submodule H D) (x : D) :
    offDiagonal H x ∈ cornerLeftIdeal H V ↔ x ∈ V := by
  change ((!![0,x;0,0] : Matrix (Fin 2) (Fin 2) D) 0 0 = 0 ∧
    (!![0,x;0,0] : Matrix (Fin 2) (Fin 2) D) 1 1 = 0 ∧
    (!![0,x;0,0] : Matrix (Fin 2) (Fin 2) D) 0 1 ∈ V) ↔ x ∈ V
  simp

theorem cornerLeftIdeal_mono (H : Subfield D) {V W : Submodule H D} (h : V ≤ W) :
    cornerLeftIdeal H V ≤ cornerLeftIdeal H W :=
  fun _ hM => ⟨hM.1,hM.2.1,h hM.2.2⟩

theorem cornerLeftIdeal_lt (H : Subfield D) {V W : Submodule H D} (h : V < W) :
    cornerLeftIdeal H V < cornerLeftIdeal H W := by
  apply lt_of_le_of_ne (cornerLeftIdeal_mono H h.le)
  intro he
  have hWV : W ≤ V := by
    intro x hx
    have hm := (offDiagonal_mem_cornerLeftIdeal H W x).mpr hx
    rw [← he] at hm
    exact (offDiagonal_mem_cornerLeftIdeal H V x).mp hm
  exact h.not_ge hWV

theorem triangular_left_ideal_chain (S : FlagSystem D) :
    StrictAnti (fun k : ℕ => cornerLeftIdeal (S.H 1) (leftTail S k)) := by
  intro i j hij
  exact cornerLeftIdeal_lt (S.H 1) (leftTail_strictAnti S hij)

theorem actual_triangular_left_ideal_chain :
    StrictAnti (fun k : ℕ => cornerLeftIdeal (actualFlagSystem.H 1) (leftTail actualFlagSystem k)) :=
  triangular_left_ideal_chain actualFlagSystem

end

end QuantumFlags

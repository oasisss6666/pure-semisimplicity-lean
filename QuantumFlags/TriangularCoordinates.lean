import QuantumFlags.RightArtinian

namespace QuantumFlags

noncomputable section

variable {D : Type*} [DivisionRing D]

def triangularSourceHom (H : Subfield D) : TriangularRing H →+* H where
  toFun r := ⟨(r : Matrix (Fin 2) (Fin 2) D) 0 0,r.property.2⟩
  map_zero' := rfl
  map_one' := by apply Subtype.ext; simp
  map_add' _ _ := rfl
  map_mul' r s := by
    apply Subtype.ext
    change ((r : Matrix (Fin 2) (Fin 2) D)*(s : Matrix (Fin 2) (Fin 2) D)) 0 0 = _
    simp [Matrix.mul_apply,Fin.sum_univ_two,s.property.1]

def triangularTargetHom (H : Subfield D) : TriangularRing H →+* D where
  toFun r := (r : Matrix (Fin 2) (Fin 2) D) 1 1
  map_zero' := rfl
  map_one' := by simp
  map_add' _ _ := rfl
  map_mul' r s := by
    change ((r : Matrix (Fin 2) (Fin 2) D)*(s : Matrix (Fin 2) (Fin 2) D)) 1 1 = _
    simp [Matrix.mul_apply,Fin.sum_univ_two,r.property.1]

def triangularCrossHom (H : Subfield D) : TriangularRing H →+ D where
  toFun r := (r : Matrix (Fin 2) (Fin 2) D) 0 1
  map_zero' := rfl
  map_add' _ _ := rfl

theorem triangularCrossHom_one (H : Subfield D) : triangularCrossHom H 1 = 0 := by
  change (1 : Matrix (Fin 2) (Fin 2) D) 0 1 = 0
  simp

theorem triangularCrossHom_mul (H : Subfield D) (r s : TriangularRing H) :
    triangularCrossHom H (r*s) =
      (triangularSourceHom H r : D)*triangularCrossHom H s+
      triangularCrossHom H r*triangularTargetHom H s := by
  change ((r : Matrix (Fin 2) (Fin 2) D)*(s : Matrix (Fin 2) (Fin 2) D)) 0 1 =
    (r : Matrix (Fin 2) (Fin 2) D) 0 0*(s : Matrix (Fin 2) (Fin 2) D) 0 1+
    (r : Matrix (Fin 2) (Fin 2) D) 0 1*(s : Matrix (Fin 2) (Fin 2) D) 1 1
  simp [Matrix.mul_apply,Fin.sum_univ_two]

theorem triangular_ext (H : Subfield D) {r s : TriangularRing H}
    (h0 : triangularSourceHom H r = triangularSourceHom H s)
    (h1 : triangularCrossHom H r = triangularCrossHom H s)
    (h2 : triangularTargetHom H r = triangularTargetHom H s) : r = s := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · exact congrArg Subtype.val h0
  · exact h1
  · exact r.property.1.trans s.property.1.symm
  · exact h2

end

end QuantumFlags

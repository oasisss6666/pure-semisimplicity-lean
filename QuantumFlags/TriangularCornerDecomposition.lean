import QuantumFlags.NonunitalCornerModules
import QuantumFlags.TriangularCoordinates

namespace QuantumFlags

noncomputable section

def productFirstCorner (A B : Type*) [Ring A] [Ring B] : A →ₙ+* A × B where
  toFun a := (a,0)
  map_zero' := rfl
  map_add' _ _ := by ext <;> simp
  map_mul' _ _ := by ext <;> simp

def productSecondCorner (A B : Type*) [Ring A] [Ring B] : B →ₙ+* A × B where
  toFun b := (0,b)
  map_zero' := rfl
  map_add' _ _ := by ext <;> simp
  map_mul' _ _ := by ext <;> simp

variable {D : Type*} [DivisionRing D]

def sourceCornerHom (H : Subfield D) : Hᵐᵒᵖ →ₙ+* (TriangularRing H)ᵐᵒᵖ :=
  (diagonalRightHom H).toNonUnitalRingHom.comp (productFirstCorner Hᵐᵒᵖ Dᵐᵒᵖ)

def targetCornerHom (H : Subfield D) : Dᵐᵒᵖ →ₙ+* (TriangularRing H)ᵐᵒᵖ :=
  (diagonalRightHom H).toNonUnitalRingHom.comp (productSecondCorner Hᵐᵒᵖ Dᵐᵒᵖ)

theorem corner_units_sum (H : Subfield D) : sourceCornerHom H 1+targetCornerHom H 1 = 1 := by
  change diagonalRightHom H (1,0)+diagonalRightHom H (0,1) = 1
  have hp : ((1,0) : Hᵐᵒᵖ × Dᵐᵒᵖ)+(0,1) = 1 := by ext <;> simp
  rw [← map_add,hp,map_one]

theorem source_target_zero (H : Subfield D) : sourceCornerHom H 1*targetCornerHom H 1 = 0 := by
  change diagonalRightHom H (1,0)*diagonalRightHom H (0,1) = 0
  have hp : ((1,0) : Hᵐᵒᵖ × Dᵐᵒᵖ)*(0,1) = 0 := by ext <;> simp
  rw [← map_mul,hp,map_zero]

theorem target_source_zero (H : Subfield D) : targetCornerHom H 1*sourceCornerHom H 1 = 0 := by
  change diagonalRightHom H (0,1)*diagonalRightHom H (1,0) = 0
  have hp : ((0,1) : Hᵐᵒᵖ × Dᵐᵒᵖ)*(1,0) = 0 := by ext <;> simp
  rw [← map_mul,hp,map_zero]

def cornerDecomposition (H : Subfield D) (M : Type*) [AddCommGroup M]
    [Module (TriangularRing H)ᵐᵒᵖ M] :
    M ≃+ cornerFixedGroup (sourceCornerHom H) M × cornerFixedGroup (targetCornerHom H) M where
  toFun x := (⟨sourceCornerHom H 1 • x,corner_projection_idempotent _ M x⟩,
    ⟨targetCornerHom H 1 • x,corner_projection_idempotent _ M x⟩)
  invFun p := (p.1 : M)+(p.2 : M)
  left_inv x := by
    change sourceCornerHom H 1 • x+targetCornerHom H 1 • x = x
    rw [← add_smul,corner_units_sum,one_smul]
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      change sourceCornerHom H 1 • ((p.1 : M)+(p.2 : M)) = (p.1 : M)
      have hc : sourceCornerHom H 1 • (p.2 : M) = 0 := by
        rw [← p.2.property,← mul_smul,source_target_zero,zero_smul]
      rw [smul_add,p.1.property,hc,add_zero]
    · apply Subtype.ext
      change targetCornerHom H 1 • ((p.1 : M)+(p.2 : M)) = (p.2 : M)
      have hc : targetCornerHom H 1 • (p.1 : M) = 0 := by
        rw [← p.1.property,← mul_smul,target_source_zero,zero_smul]
      rw [smul_add,hc,p.2.property,zero_add]
  map_add' x y := by
    apply Prod.ext <;> apply Subtype.ext
    · exact smul_add (sourceCornerHom H 1) x y
    · exact smul_add (targetCornerHom H 1) x y

theorem cornerDecomposition_components (H : Subfield D) (M : Type*) [AddCommGroup M]
    [Module (TriangularRing H)ᵐᵒᵖ M] (x : M) :
    (((cornerDecomposition H M x).1 : M),((cornerDecomposition H M x).2 : M)) =
      (sourceCornerHom H 1 • x,targetCornerHom H 1 • x) := rfl

end

end QuantumFlags

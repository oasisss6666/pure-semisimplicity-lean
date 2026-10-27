import QuantumFlags.StripDuality

namespace QuantumFlags

noncomputable section

variable {D : Type*} [DivisionRing D]

def stripLeftMultiplication (S : FlagSystem D) (k : ℕ) (f : S.H k) :
    StripSpace S k →ₗ[(S.H (k+1))ᵐᵒᵖ] StripSpace S k where
  toFun x := f • x
  map_add' x y := smul_add f x y
  map_smul' r x := smul_comm f r x

theorem leftMultiplication_coordinates (S : FlagSystem D) (k : ℕ) (f : S.H k)
    (ab : Fin 2 → S.H (k+1)) :
    stripLeftMultiplication S k f (rightStripEquiv S k ab) =
      rightStripEquiv S k ![firstColumn S k f 0*ab 0+secondColumn S k f 0*ab 1,
        firstColumn S k f 1*ab 0+secondColumn S k f 1*ab 1] := by
  apply Subtype.ext
  have hf := firstColumn_eval S k f
  have hft := secondColumn_eval S k f
  simp only [rightEval, Subfield.subtype_apply] at hf hft
  change (f : D)*((ab 0 : D)+S.t*(ab 1 : D)) =
    ((firstColumn S k f 0*ab 0+secondColumn S k f 0*ab 1 : S.H (k+1)) : D)+
    S.t*(firstColumn S k f 1*ab 0+secondColumn S k f 1*ab 1 : S.H (k+1))
  simp only [Subfield.coe_add, Subfield.coe_mul]
  calc
    _ = (f : D)*(ab 0 : D)+((f : D)*S.t)*(ab 1 : D) := by noncomm_ring
    _ = _ := by rw [← hft, ← hf]; noncomm_ring

theorem rightMultiplication_coordinates (S : FlagSystem D) (k : ℕ) (f : S.H k)
    (uv : Fin 2 → S.H (k+1)) :
    MulOpposite.op (reciprocalEquiv S k f) • leftStripEquiv S k uv =
      leftStripEquiv S k ![-uv 1*secondColumn S k f 0+uv 0*secondColumn S k f 1,
        uv 1*firstColumn S k f 0-uv 0*firstColumn S k f 1] := by
  apply Subtype.ext
  change ((uv 0 : D)+(uv 1 : D)*S.t)*reciprocalValue S k f =
    ((-uv 1*secondColumn S k f 0+uv 0*secondColumn S k f 1 : S.H (k+1)) : D)+
    (uv 1*firstColumn S k f 0-uv 0*firstColumn S k f 1 : S.H (k+1))*S.t
  simp only [Subfield.coe_add, Subfield.coe_sub, Subfield.coe_mul, Subfield.coe_neg]
  calc
    _ = (uv 0 : D)*reciprocalValue S k f+(uv 1 : D)*(S.t*reciprocalValue S k f) := by
      noncomm_ring
    _ = (uv 0 : D)*((secondColumn S k f 1 : D)-(firstColumn S k f 1 : D)*S.t)+
        (uv 1 : D)*((firstColumn S k f 0 : D)*S.t-(secondColumn S k f 0 : D)) := by
      rw [variable_mul_reciprocalValue]; rfl
    _ = _ := by noncomm_ring

/-- The twist identity in Proposition 4.3, in the actual right-linear Hom space. -/
theorem stripDualEquiv_twist (S : FlagSystem D) (k : ℕ) (z : StripSpace S (k+1))
    (f : S.H k) :
    (stripDualEquiv S k z).comp (stripLeftMultiplication S k f) =
      stripDualEquiv S k (MulOpposite.op (reciprocalEquiv S k f) • z) := by
  obtain ⟨uv,rfl⟩ := (leftStripEquiv S k).surjective z
  apply LinearMap.ext
  intro x
  obtain ⟨ab,rfl⟩ := (rightStripEquiv S k).surjective x
  rw [LinearMap.comp_apply, leftMultiplication_coordinates, rightMultiplication_coordinates,
    stripDualEquiv_formula, stripDualEquiv_formula]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  noncomm_ring

theorem actual_strip_duality (k : ℕ) :
    Nonempty (StripSpace actualFlagSystem (k+1) ≃ₗ[actualFlagSystem.H (k+1)]
      StripRightDual actualFlagSystem k) :=
  ⟨stripDualEquiv actualFlagSystem k⟩

end

end QuantumFlags

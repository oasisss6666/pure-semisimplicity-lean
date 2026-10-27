import QuantumFlags.StripCoordinates

namespace QuantumFlags

noncomputable section

variable {D : Type*} [DivisionRing D]

def stripRightSubmodule (S : FlagSystem D) (k : ℕ) : Submodule (S.H (k+1))ᵐᵒᵖ D where
  carrier := strip S k
  zero_mem' := strip_zero_mem S k
  add_mem' := strip_add_mem S k
  smul_mem' r x hx := strip_right_mul S k r.unop r.unop.property x hx

def stripLeftSubmodule (S : FlagSystem D) (k : ℕ) : Submodule (S.H k) D where
  carrier := strip S k
  zero_mem' := strip_zero_mem S k
  add_mem' := strip_add_mem S k
  smul_mem' r x hx := strip_left_mul S k r r.property x hx

abbrev StripSpace (S : FlagSystem D) (k : ℕ) := stripRightSubmodule S k

instance stripLeftModule (S : FlagSystem D) (k : ℕ) : Module (S.H k) (StripSpace S k) :=
  inferInstanceAs (Module (S.H k) (stripLeftSubmodule S k))

theorem strip_right_smul (S : FlagSystem D) (k : ℕ)
    (r : (S.H (k+1))ᵐᵒᵖ) (x : StripSpace S k) :
    ((r • x : StripSpace S k) : D) = (x : D)*(r.unop : D) := rfl

theorem strip_left_smul (S : FlagSystem D) (k : ℕ)
    (r : S.H k) (x : StripSpace S k) :
    ((r • x : StripSpace S k) : D) = (r : D)*(x : D) := rfl

instance strip_smul_comm (S : FlagSystem D) (k : ℕ) :
    SMulCommClass (S.H k) (S.H (k+1))ᵐᵒᵖ (StripSpace S k) where
  smul_comm a b x := Subtype.ext (mul_assoc (a : D) x (b.unop : D)).symm

def rightStripLinear (S : FlagSystem D) (k : ℕ) :
    (Fin 2 → S.H (k+1)) →ₗ[(S.H (k+1))ᵐᵒᵖ] StripSpace S k where
  toFun c := ⟨rightEval (S.H (k+1)).subtype S.t c, ⟨c,rfl⟩⟩
  map_add' c d := by
    apply Subtype.ext
    change rightEval (S.H (k+1)).subtype S.t (c+d) =
      rightEval (S.H (k+1)).subtype S.t c+rightEval (S.H (k+1)).subtype S.t d
    simp only [rightEval, Subfield.subtype_apply, Pi.add_apply, Subfield.coe_add]
    noncomm_ring
  map_smul' r c := by
    apply Subtype.ext
    change (((c 0*r.unop : S.H (k+1)) : D)+S.t*(c 1*r.unop : S.H (k+1))) =
      ((c 0 : D)+S.t*(c 1 : D))*(r.unop : D)
    simp only [Subfield.coe_mul]
    noncomm_ring

theorem rightStripLinear_bijective (S : FlagSystem D) (k : ℕ) :
    Function.Bijective (rightStripLinear S k) := by
  constructor
  · intro c d h
    exact strip_right_injective S k (congrArg Subtype.val h)
  · intro x
    obtain ⟨c,hc⟩ := x.property
    exact ⟨c, Subtype.ext hc⟩

def rightStripEquiv (S : FlagSystem D) (k : ℕ) :
    (Fin 2 → S.H (k+1)) ≃ₗ[(S.H (k+1))ᵐᵒᵖ] StripSpace S k :=
  LinearEquiv.ofBijective (rightStripLinear S k) (rightStripLinear_bijective S k)

def leftStripLinear (S : FlagSystem D) (k : ℕ) :
    (Fin 2 → S.H (k+1)) →ₗ[S.H (k+1)] StripSpace S (k+1) where
  toFun c := ⟨leftEval (S.H (k+1)).subtype S.t c, by
    change leftEval (S.H (k+1)).subtype S.t c ∈ strip S (k+1)
    rw [strip_eq_left S (k+1) (by omega)]; exact ⟨c,rfl⟩⟩
  map_add' c d := by
    apply Subtype.ext
    change leftEval (S.H (k+1)).subtype S.t (c+d) =
      leftEval (S.H (k+1)).subtype S.t c+leftEval (S.H (k+1)).subtype S.t d
    simp only [leftEval, Subfield.subtype_apply, Pi.add_apply, Subfield.coe_add]
    noncomm_ring
  map_smul' r c := by
    apply Subtype.ext
    change (((r*c 0 : S.H (k+1)) : D)+(r*c 1 : S.H (k+1))*S.t) =
      (r : D)*((c 0 : D)+(c 1 : D)*S.t)
    simp only [Subfield.coe_mul]
    noncomm_ring

theorem leftStripLinear_bijective (S : FlagSystem D) (k : ℕ) :
    Function.Bijective (leftStripLinear S k) := by
  constructor
  · intro c d h
    exact (S.adjacent (k+1) (by omega)).1 (congrArg Subtype.val h)
  · intro x
    have hx : (x : D) ∈ strip S (k+1) := x.property
    rw [strip_eq_left S (k+1) (by omega)] at hx
    obtain ⟨c,hc⟩ := hx
    exact ⟨c,Subtype.ext hc⟩

def leftStripEquiv (S : FlagSystem D) (k : ℕ) :
    (Fin 2 → S.H (k+1)) ≃ₗ[S.H (k+1)] StripSpace S (k+1) :=
  LinearEquiv.ofBijective (leftStripLinear S k) (leftStripLinear_bijective S k)

theorem rightStripEquiv_value (S : FlagSystem D) (k : ℕ) (c : Fin 2 → S.H (k+1)) :
    (rightStripEquiv S k c : D) = (c 0 : D)+S.t*(c 1 : D) := rfl

theorem leftStripEquiv_value (S : FlagSystem D) (k : ℕ) (c : Fin 2 → S.H (k+1)) :
    (leftStripEquiv S k c : D) = (c 0 : D)+(c 1 : D)*S.t := rfl

end

end QuantumFlags

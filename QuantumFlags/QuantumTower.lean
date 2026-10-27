import QuantumFlags.SkewExtension

/-!
# The tower of quantum division rings for an arbitrary parameter

Manuscript Section 2.5 (source lines 167-195), for an arbitrary `q ∈ ℚ^×`.  Put `T_0 = ℚ` and
`T_1 = T_0(t_1; id) = ℚ(t_1)`.  For `n ≥ 1` the automorphism `τ_n` of `T_n` fixes `T_{n-1}` and
sends `t_n` to `q t_n`, and `T_{n+1} = T_n(t_{n+1}; τ_n)` is the division ring of fractions of the
skew polynomial ring `T_n[t_{n+1}; τ_n]`.  Here `τ_0` is the identity of `ℚ`.

The tower used for the counterexample, `OreLevel`, is the instance `q = 1/2`.
-/

namespace QuantumFlags

noncomputable section

structure SkewStage where
  Carrier : Type
  [divisionRing : DivisionRing Carrier]
  [charZero : CharZero Carrier]
  automorphism : Carrier ≃+* Carrier

attribute [instance] SkewStage.divisionRing SkewStage.charZero

def initialStage : SkewStage where
  Carrier := ℚ
  divisionRing := inferInstance
  charZero := inferInstance
  automorphism := RingEquiv.refl ℚ

/-- `T_{n+1} = T_n(t_{n+1}; τ_n)`, with the automorphism `τ_{n+1}` fixing `T_n` and scaling
`t_{n+1}` by `q`. -/
def quantumNextStage (q : ℚ) (hq : q ≠ 0) (S : SkewStage) : SkewStage where
  Carrier := SkewExtension S.Carrier S.automorphism
  divisionRing := inferInstance
  charZero := inferInstance
  automorphism := extensionScalingAut S.automorphism ((q : ℚ) : S.Carrier)
    (fun a => Rat.cast_commute _ a) (by exact_mod_cast hq)

def quantumStage (q : ℚ) (hq : q ≠ 0) : ℕ → SkewStage
  | 0 => initialStage
  | n+1 => quantumNextStage q hq (quantumStage q hq n)

variable (q : ℚ) (hq : q ≠ 0)

/-- The division ring `T_n`. -/
abbrev QuantumLevel (n : ℕ) := (quantumStage q hq n).Carrier

/-- The inclusion `T_n ⊆ T_{n+1}`. -/
def quantumStep (n : ℕ) : QuantumLevel q hq n →+* QuantumLevel q hq (n+1) :=
  extensionConstants (quantumStage q hq n).automorphism

/-- The generator `t_{n+1} ∈ T_{n+1}`. -/
def quantumGenerator (n : ℕ) : QuantumLevel q hq (n+1) :=
  extensionVariable (quantumStage q hq n).automorphism

/-- The automorphism `τ_n` of `T_n` (the identity for `n = 0`). -/
def quantumAutomorphism (n : ℕ) : QuantumLevel q hq n ≃+* QuantumLevel q hq n :=
  (quantumStage q hq n).automorphism

theorem quantumAutomorphism_zero (a : QuantumLevel q hq 0) : quantumAutomorphism q hq 0 a = a :=
  rfl

theorem quantumAutomorphism_fixes (n : ℕ) (a : QuantumLevel q hq n) :
    quantumAutomorphism q hq (n+1) (quantumStep q hq n a) = quantumStep q hq n a :=
  extensionScalingAut_constants _ _ _ _ a

theorem quantumAutomorphism_scales (n : ℕ) :
    quantumAutomorphism q hq (n+1) (quantumGenerator q hq n) =
      ((q : ℚ) : QuantumLevel q hq (n+1)) * quantumGenerator q hq n := by
  change extensionScalingAut _ _ _ _ (extensionVariable _) = _
  rw [extensionScalingAut_variable, map_ratCast]
  rfl

theorem quantumGenerator_relation (n : ℕ) (a : QuantumLevel q hq n) :
    quantumGenerator q hq n * quantumStep q hq n a =
      quantumStep q hq n (quantumAutomorphism q hq n a) * quantumGenerator q hq n :=
  extension_variable_relation _ a

end

end QuantumFlags

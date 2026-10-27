import QuantumFlags.ActualQuantumChain

namespace QuantumFlags

noncomputable section

variable {D : Type*} [DivisionRing D]

/-- The exact input to Section 4. The subdivision rings need not be nested. -/
structure FlagSystem (D : Type*) [DivisionRing D] where
  t : D
  H : ℕ → Subfield D
  zero : H 0 = ⊤
  right_basis : ∀ r, Function.Bijective
    (wideEval (H r).subtype (fun i : Fin (r+1) => t^i.val))
  adjacent : ∀ p, 1 ≤ p →
    Function.Injective (leftEval (H p).subtype t) ∧
    Function.Injective (rightEval (H (p+1)).subtype t) ∧
    Set.range (leftEval (H p).subtype t) = Set.range (rightEval (H (p+1)).subtype t)

theorem imageField_zero [CharZero D] (Q : QuantumChain D) (B : PowerChainProperties Q) :
    imageField Q 0 = ⊤ := by
  apply top_unique
  intro a _
  obtain ⟨c, hc⟩ := (chain_global_right_basis Q B 0).surjective a
  have he : (c 0 : D) = a := by
    simpa [wideEval, Fin.sum_univ_one] using hc
  exact he ▸ (c 0).property

def actualFlagSystem : FlagSystem OreUnion where
  t := oreVariable 0
  H := imageField actualQuantumChain
  zero := imageField_zero actualQuantumChain actualPowerChainProperties
  right_basis := actual_global_right_basis
  adjacent := actual_global_adjacent_flags

theorem flagSystem_exists : Nonempty (FlagSystem OreUnion) := ⟨actualFlagSystem⟩

end

end QuantumFlags

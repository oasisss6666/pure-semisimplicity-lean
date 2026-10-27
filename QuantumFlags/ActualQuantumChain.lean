import QuantumFlags.OreChainImages
import QuantumFlags.GlobalBasis

namespace QuantumFlags

noncomputable section

theorem ore_right_pair (n : ℕ) :
    Function.Injective (rightEval (oreLayer n).subtype (oreVariable n)) := by
  intro c d h
  apply ore_right_powers n 1
  simpa only [Nat.reduceAdd, wideEval, rightEval, Fin.sum_univ_two, Fin.val_zero, Fin.val_one,
    pow_zero, pow_one, one_mul] using h

theorem ore_left_pair (n : ℕ) :
    Function.Injective (leftEval (oreLayer n).subtype (oreVariable n)) := by
  intro c d h
  apply ore_left_powers n 1
  simpa only [Nat.reduceAdd, leftEval, Subfield.subtype_apply, Fin.sum_univ_two, Fin.val_zero,
    Fin.val_one, pow_zero, pow_one, mul_one] using h

/-- A constructed model. None of the quantum-chain properties is an input. -/
def actualQuantumChain : QuantumChain OreUnion where
  x := oreVariable
  layer := oreLayer
  increasing := oreLayer_increasing
  covers := oreLayer_covers
  generator_mem := oreVariable_mem
  not_rational := oreVariable_not_rational
  adjacent := ore_adjacent
  distant := ore_distant
  remote := ore_remote
  normalizer := oreNormalizer
  normalizes := oreVariable_normalizes
  right_pair_independent := ore_right_pair
  left_pair_independent := ore_left_pair

theorem actualPowerChainProperties : PowerChainProperties actualQuantumChain where
  fixes_previous := oreNormalizer_fixes
  scales_previous := oreNormalizer_scales
  right_powers_independent := ore_right_powers

theorem actualQuantumChain_exists :
    ∃ Q : QuantumChain OreUnion, PowerChainProperties Q :=
  ⟨actualQuantumChain, actualPowerChainProperties⟩

/-- The manuscript's (B) for the actual Ore division-ring construction. -/
theorem actual_global_right_basis (r : ℕ) :
    Function.Bijective (wideEval (imageField actualQuantumChain r).subtype
      (fun i : Fin (r+1) => (oreVariable 0)^i.val)) :=
  chain_global_right_basis actualQuantumChain actualPowerChainProperties r

/-- The manuscript's (F) for the actual Ore division-ring construction. -/
theorem actual_global_adjacent_flags (p : ℕ) (hp : 1 ≤ p) :
    Function.Injective (leftEval (imageField actualQuantumChain p).subtype (oreVariable 0)) ∧
    Function.Injective (rightEval (imageField actualQuantumChain (p+1)).subtype (oreVariable 0)) ∧
    Set.range (leftEval (imageField actualQuantumChain p).subtype (oreVariable 0)) =
      Set.range (rightEval (imageField actualQuantumChain (p+1)).subtype (oreVariable 0)) :=
  chain_global_adjacent_flags actualQuantumChain p hp

end

end QuantumFlags

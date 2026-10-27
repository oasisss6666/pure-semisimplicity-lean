import QuantumFlags.OreTower
import QuantumFlags.PowerChain

namespace QuantumFlags

noncomputable section

abbrev oreLayer (n : ℕ) : Subfield OreUnion := (oreEmbed n).fieldRange

def oreVariable (n : ℕ) : OreUnion := oreEmbed (n+1) (oreGenerator n)

theorem oreLayer_increasing : Monotone oreLayer := by
  intro n m h a ha
  obtain ⟨b, rfl⟩ := RingHom.mem_fieldRange.mp ha
  exact RingHom.mem_fieldRange.mpr ⟨oreMap n m h b, oreEmbed_map n m h b⟩

theorem oreLayer_covers (a : OreUnion) : ∃ n, a ∈ oreLayer n := by
  obtain ⟨n, b, rfl⟩ := DirectLimit.exists_eq_mk oreMap a
  exact ⟨n, RingHom.mem_fieldRange.mpr ⟨b, rfl⟩⟩

theorem oreVariable_mem (n : ℕ) : oreVariable n ∈ oreLayer (n+1) :=
  (oreEmbed (n+1)).mem_fieldRange_self _

abbrev oreLayerEquiv (n : ℕ) : OreLevel n ≃+* oreLayer n :=
  (oreEmbed n).rangeRestrictFieldEquiv

def oreNormalizer (n : ℕ) : oreLayer n ≃+* oreLayer n :=
  (oreLayerEquiv n).symm.trans ((oreAutomorphism n).trans (oreLayerEquiv n))

theorem oreNormalizer_image (n : ℕ) (a : OreLevel n) :
    oreNormalizer n (oreLayerEquiv n a) = oreLayerEquiv n (oreAutomorphism n a) := by
  simp only [oreNormalizer, RingEquiv.trans_apply, RingEquiv.symm_apply_apply]

theorem oreVariable_normalizes (n : ℕ) (a : oreLayer n) :
    oreVariable n * (a : OreUnion) = (oreNormalizer n a : OreUnion)*oreVariable n := by
  obtain ⟨b, rfl⟩ := (oreLayerEquiv n).surjective a
  rw [oreNormalizer_image]
  have he := congrArg (oreEmbed (n+1)) (oreGenerator_relation n b)
  simpa only [map_mul, oreEmbed_step, RingHom.rangeRestrictFieldEquiv_apply_coe,
    oreVariable] using he

theorem oreVariable_not_rational (n : ℕ) : NotRational (oreVariable n) := by
  intro r he
  apply oreGenerator_notRational n r
  apply (oreEmbed (n+1)).injective
  simpa only [map_ratCast, oreVariable] using he

theorem oreLayerEquiv_step (n : ℕ) (a : OreLevel n) :
    oreLayerEquiv (n+1) (oreStep n a) =
      Subfield.inclusion (oreLayer_increasing (Nat.le_succ n)) (oreLayerEquiv n a) := by
  apply Subtype.ext
  exact oreEmbed_step n a

theorem oreNormalizer_fixes (n : ℕ) (a : oreLayer n) :
    oreNormalizer (n+1) (Subfield.inclusion (oreLayer_increasing (Nat.le_succ n)) a) =
      Subfield.inclusion (oreLayer_increasing (Nat.le_succ n)) a := by
  obtain ⟨b, rfl⟩ := (oreLayerEquiv n).surjective a
  rw [← oreLayerEquiv_step, oreNormalizer_image, oreAutomorphism_fixes]

theorem oreNormalizer_scales (n : ℕ) :
    oreNormalizer (n+1) ⟨oreVariable n, oreVariable_mem n⟩ =
      half (oreLayer (n+1))*⟨oreVariable n, oreVariable_mem n⟩ := by
  have he : (⟨oreVariable n, oreVariable_mem n⟩ : oreLayer (n+1)) =
      oreLayerEquiv (n+1) (oreGenerator n) := rfl
  rw [he, oreNormalizer_image, oreAutomorphism_scales, map_mul, map_ratCast]
  rfl

theorem ore_adjacent (n : ℕ) :
    oreVariable (n+1)*oreVariable n = half OreUnion*oreVariable n*oreVariable (n+1) := by
  have he := oreVariable_normalizes (n+1) ⟨oreVariable n, oreVariable_mem n⟩
  rw [oreNormalizer_scales] at he
  exact he

theorem ore_remote (n : ℕ) (a : OreUnion) (ha : a ∈ oreLayer n) :
    Commute a (oreVariable (n+1)) := by
  have he := oreVariable_normalizes (n+1)
    (Subfield.inclusion (oreLayer_increasing (Nat.le_succ n)) ⟨a, ha⟩)
  rw [oreNormalizer_fixes] at he
  exact he.symm

theorem ore_distant (i j : ℕ) (h : i+1 < j) : Commute (oreVariable i) (oreVariable j) := by
  cases j with
  | zero => omega
  | succ j =>
    exact ore_remote j _ (oreLayer_increasing (by omega) (oreVariable_mem i))

theorem ore_right_powers (n r : ℕ) :
    Function.Injective (wideEval (oreLayer n).subtype
      (fun h : Fin (r+1) => (oreVariable n)^h.val)) := by
  intro c d h
  have he : (fun i => (oreLayerEquiv n).symm (c i)) =
      (fun i => (oreLayerEquiv n).symm (d i)) := by
    apply oreLevel_right_powers n r
    apply (oreEmbed (n+1)).injective
    simpa only [map_sum, map_mul, map_pow, oreEmbed_step, wideEval,
      RingHom.rangeRestrictFieldEquiv_apply_symm_apply, oreVariable,
      Subfield.subtype_apply] using h
  funext i
  exact (oreLayerEquiv n).symm.injective (congrFun he i)

theorem ore_left_powers (n r : ℕ) :
    Function.Injective (fun c : Fin (r+1) → oreLayer n =>
      ∑ i, (c i : OreUnion)*(oreVariable n)^i.val) := by
  intro c d h
  have he : (fun i => (oreLayerEquiv n).symm (c i)) =
      (fun i => (oreLayerEquiv n).symm (d i)) := by
    apply oreLevel_left_powers n r
    apply (oreEmbed (n+1)).injective
    simpa only [map_sum, map_mul, map_pow, oreEmbed_step,
      RingHom.rangeRestrictFieldEquiv_apply_symm_apply, oreVariable] using h
  funext i
  exact (oreLayerEquiv n).symm.injective (congrFun he i)

end

end QuantumFlags

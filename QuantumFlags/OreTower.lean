import QuantumFlags.QuantumTower
import Mathlib.Algebra.Colimit.DirectLimit

namespace QuantumFlags

noncomputable section

/-- The tower of the counterexample: the quantum tower with parameter `q = 1/2`. -/
def oreStage : ℕ → SkewStage := quantumStage (1/2) (by norm_num)

abbrev OreLevel (n : ℕ) := (oreStage n).Carrier

def oreStep (n : ℕ) : OreLevel n →+* OreLevel (n+1) :=
  extensionConstants (oreStage n).automorphism

def oreGenerator (n : ℕ) : OreLevel (n+1) :=
  extensionVariable (oreStage n).automorphism

def oreAutomorphism (n : ℕ) : OreLevel n ≃+* OreLevel n :=
  (oreStage n).automorphism

theorem oreAutomorphism_fixes (n : ℕ) (a : OreLevel n) :
    oreAutomorphism (n+1) (oreStep n a) = oreStep n a :=
  extensionScalingAut_constants _ _ _ _ a

theorem oreAutomorphism_scales (n : ℕ) :
    oreAutomorphism (n+1) (oreGenerator n) = ((1/2 : ℚ) : OreLevel (n+1))*oreGenerator n := by
  change extensionScalingAut _ _ _ _ (extensionVariable _) = _
  rw [extensionScalingAut_variable, map_ratCast]
  rfl

theorem oreGenerator_relation (n : ℕ) (a : OreLevel n) :
    oreGenerator n * oreStep n a = oreStep n (oreAutomorphism n a) * oreGenerator n :=
  extension_variable_relation _ a

theorem oreGenerator_notRational (n : ℕ) : NotRational (oreGenerator n) :=
  extensionVariable_notRational _

theorem oreLevel_left_powers (n r : ℕ) :
    Function.Injective (fun c : Fin (r+1) → OreLevel n =>
      ∑ i, oreStep n (c i)*oreGenerator n ^ i.val) :=
  extension_left_powers_independent _ r

theorem oreLevel_right_powers (n r : ℕ) :
    Function.Injective (fun c : Fin (r+1) → OreLevel n =>
      ∑ i, oreGenerator n ^ i.val*oreStep n (c i)) :=
  extension_right_powers_independent _ r

def oreMap (n m : ℕ) (h : n ≤ m) : OreLevel n →+* OreLevel m :=
  Nat.leRecOn h (fun {k} f => (oreStep k).comp f) (RingHom.id _)

theorem oreMap_self (n : ℕ) : oreMap n n le_rfl = RingHom.id _ :=
  Nat.leRecOn_self _

theorem oreMap_succ (n m : ℕ) (h : n ≤ m) :
    oreMap n (m+1) (h.trans (Nat.le_succ m)) = (oreStep m).comp (oreMap n m h) :=
  Nat.leRecOn_succ h _

theorem oreMap_comp (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) :
    (oreMap j k hjk).comp (oreMap i j hij) = oreMap i k (hij.trans hjk) := by
  induction k, hjk using Nat.le_induction with
  | base => rw [oreMap_self]; rfl
  | succ k hjk ih =>
    rw [oreMap_succ j k hjk, oreMap_succ i k (hij.trans hjk), RingHom.comp_assoc, ih]

instance oreDirectedSystem : DirectedSystem OreLevel (oreMap · · ·) where
  map_self {i} x := by rw [oreMap_self]; rfl
  map_map {k j i} hij hjk x := DFunLike.congr_fun (oreMap_comp i j k hij hjk) x

abbrev OreUnion := DirectLimit OreLevel oreMap

def oreEmbed (n : ℕ) : OreLevel n →+* OreUnion := DirectLimit.Ring.of OreLevel oreMap n

theorem oreEmbed_map (n m : ℕ) (h : n ≤ m) (a : OreLevel n) :
    oreEmbed m (oreMap n m h a) = oreEmbed n a :=
  DirectLimit.Ring.of_f h a

theorem oreEmbed_step (n : ℕ) (a : OreLevel n) :
    oreEmbed (n+1) (oreStep n a) = oreEmbed n a := by
  have he := oreEmbed_map n (n+1) (Nat.le_succ n) a
  rw [oreMap_succ n n le_rfl, oreMap_self] at he
  simpa only [RingHom.comp_apply, RingHom.id_apply] using he

instance oreUnion_charZero : CharZero OreUnion where
  cast_injective m n h := by
    have he : (m : OreLevel 0) = (n : OreLevel 0) :=
      (oreEmbed 0).injective (by simpa only [map_natCast] using h)
    exact Nat.cast_injective he

end

end QuantumFlags

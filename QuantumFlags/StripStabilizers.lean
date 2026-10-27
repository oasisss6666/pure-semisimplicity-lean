import QuantumFlags.AllWidthFlags

namespace QuantumFlags

noncomputable section

variable {D : Type*} [DivisionRing D]

def leftTripleEval (H : Subfield D) (t : D) (c : Fin 3 → H) : D :=
  (c 0 : D)+(c 1 : D)*t+(c 2 : D)*t^2

def rightTripleEval (H : Subfield D) (t : D) (c : Fin 3 → H) : D :=
  (c 0 : D)+t*(c 1 : D)+t^2*(c 2 : D)

theorem leftTripleEval_injective (S : FlagSystem D) (p : ℕ) (hp : 1 ≤ p) :
    Function.Injective (leftTripleEval (S.H p) S.t) := by
  simpa [Function.Injective, leftPowerEval, leftTripleEval, Fin.sum_univ_succ, add_assoc] using
    leftPowerEval_injective S p hp 2

theorem rightTripleEval_injective (S : FlagSystem D) (k : ℕ) :
    Function.Injective (rightTripleEval (S.H (k+2)) S.t) := by
  simpa [Function.Injective, wideEval, rightTripleEval, Fin.sum_univ_succ, add_assoc] using
    flag_right_prefix_injective S k 2

def strip (S : FlagSystem D) (k : ℕ) : Set D :=
  Set.range (rightEval (S.H (k+1)).subtype S.t)

theorem one_mem_strip (S : FlagSystem D) (k : ℕ) : (1 : D) ∈ strip S k :=
  ⟨![1, 0], by simp [rightEval]⟩

theorem variable_mem_strip (S : FlagSystem D) (k : ℕ) : S.t ∈ strip S k :=
  ⟨![0, 1], by simp [rightEval]⟩

theorem strip_zero (S : FlagSystem D) : strip S 0 = Set.univ := by
  ext a
  constructor
  · intro _; trivial
  · intro _
    obtain ⟨c, hc⟩ := (S.right_basis 1).surjective a
    refine ⟨c, ?_⟩
    simpa [wideEval, rightEval, Fin.sum_univ_two] using hc

theorem strip_eq_left (S : FlagSystem D) (k : ℕ) (hk : 1 ≤ k) :
    strip S k = Set.range (leftEval (S.H k).subtype S.t) :=
  (S.adjacent k hk).2.2.symm

theorem strip_left_mul (S : FlagSystem D) (k : ℕ) (f : D) (hf : f ∈ S.H k)
    (a : D) (ha : a ∈ strip S k) : f*a ∈ strip S k := by
  cases k with
  | zero => rw [strip_zero]; trivial
  | succ k =>
    rw [strip_eq_left S (k+1) (by omega)] at ha ⊢
    obtain ⟨c, rfl⟩ := ha
    refine ⟨![(⟨f, hf⟩ : S.H (k+1))*c 0, (⟨f, hf⟩ : S.H (k+1))*c 1], ?_⟩
    simp [leftEval, mul_add, mul_assoc]

theorem strip_right_mul (S : FlagSystem D) (k : ℕ) (f : D) (hf : f ∈ S.H (k+1))
    (a : D) (ha : a ∈ strip S k) : a*f ∈ strip S k := by
  obtain ⟨c, rfl⟩ := ha
  refine ⟨![c 0*(⟨f, hf⟩ : S.H (k+1)), c 1*(⟨f, hf⟩ : S.H (k+1))], ?_⟩
  simp [rightEval, add_mul, mul_assoc]

/-- The first equality in Proposition 4.2, including k=0. -/
theorem strip_left_stabilizer (S : FlagSystem D) (k : ℕ) (f : D) :
    (∀ a ∈ strip S k, f*a ∈ strip S k) ↔ f ∈ S.H k := by
  constructor
  · intro hf
    cases k with
    | zero => rw [S.zero]; trivial
    | succ k =>
      have hk : 1 ≤ k+1 := by omega
      have hfm : f ∈ strip S (k+1) := by
        simpa only [mul_one] using hf 1 (one_mem_strip S (k+1))
      have hftm := hf S.t (variable_mem_strip S (k+1))
      rw [strip_eq_left S (k+1) hk] at hfm hftm
      obtain ⟨a, ha⟩ := hfm
      obtain ⟨b, hb⟩ := hftm
      have he : leftTripleEval (S.H (k+1)) S.t ![0, a 0, a 1] =
          leftTripleEval (S.H (k+1)) S.t ![b 0, b 1, 0] := by
        rw [← ha] at hb
        simpa [leftTripleEval, leftEval, pow_two, add_mul, mul_assoc] using hb.symm
      have hcoeff := leftTripleEval_injective S (k+1) hk he
      have hz : a 1 = 0 := by simpa using congrFun hcoeff (2 : Fin 3)
      have hfa : f = (a 0 : D) := by rw [← ha]; simp [leftEval, hz]
      rw [hfa]
      exact (a 0).property
  · exact fun hf a ha => strip_left_mul S k f hf a ha

/-- The second equality in Proposition 4.2. -/
theorem strip_right_stabilizer (S : FlagSystem D) (k : ℕ) (g : D) :
    (∀ a ∈ strip S (k+1), a*g ∈ strip S (k+1)) ↔ g ∈ S.H (k+2) := by
  constructor
  · intro hg
    have hgm : g ∈ strip S (k+1) := by
      simpa only [one_mul] using hg 1 (one_mem_strip S (k+1))
    have htgm := hg S.t (variable_mem_strip S (k+1))
    obtain ⟨a, ha⟩ := hgm
    obtain ⟨b, hb⟩ := htgm
    have he : rightTripleEval (S.H (k+2)) S.t ![0, a 0, a 1] =
        rightTripleEval (S.H (k+2)) S.t ![b 0, b 1, 0] := by
      rw [← ha] at hb
      simpa [rightTripleEval, rightEval, pow_two, mul_add, mul_assoc] using hb.symm
    have hcoeff := rightTripleEval_injective S k he
    have hz : a 1 = 0 := by simpa using congrFun hcoeff (2 : Fin 3)
    have hga : g = (a 0 : D) := by rw [← ha]; simp [rightEval, hz]
    rw [hga]
    exact (a 0).property
  · exact fun hg a ha => strip_right_mul S (k+1) g hg a ha

theorem actual_strip_stabilizers (k : ℕ) :
    (∀ f : OreUnion, (∀ a ∈ strip actualFlagSystem k, f*a ∈ strip actualFlagSystem k) ↔
      f ∈ imageField actualQuantumChain k) ∧
    (∀ g : OreUnion, (∀ a ∈ strip actualFlagSystem (k+1), a*g ∈ strip actualFlagSystem (k+1)) ↔
      g ∈ imageField actualQuantumChain (k+2)) :=
  ⟨strip_left_stabilizer actualFlagSystem k, strip_right_stabilizer actualFlagSystem k⟩

end

end QuantumFlags

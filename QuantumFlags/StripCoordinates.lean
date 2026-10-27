import QuantumFlags.StripStabilizers

namespace QuantumFlags

noncomputable section

variable {D : Type*} [DivisionRing D]

theorem strip_right_injective (S : FlagSystem D) (k : ℕ) :
    Function.Injective (rightEval (S.H (k+1)).subtype S.t) := by
  simpa [Function.Injective, wideEval, rightEval, Nat.reduceAdd, Fin.sum_univ_two] using
    flag_right_prefix_injective S k 1

theorem strip_zero_mem (S : FlagSystem D) (k : ℕ) : (0 : D) ∈ strip S k :=
  ⟨0, by simp [rightEval]⟩

theorem strip_add_mem (S : FlagSystem D) (k : ℕ) {x y : D}
    (hx : x ∈ strip S k) (hy : y ∈ strip S k) : x+y ∈ strip S k := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  refine ⟨a+b, ?_⟩
  simp [rightEval, mul_add]
  abel

theorem strip_neg_mem (S : FlagSystem D) (k : ℕ) {x : D}
    (hx : x ∈ strip S k) : -x ∈ strip S k := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨-a, by simp [rightEval]; abel⟩

theorem strip_pair_criterion (S : FlagSystem D) (k : ℕ) (f : D) :
    (f ∈ strip S k ∧ f*S.t ∈ strip S k) ↔ f ∈ S.H k := by
  constructor
  · rintro ⟨hf, hft⟩
    apply (strip_left_stabilizer S k f).mp
    rintro x ⟨a, rfl⟩
    have h0 := strip_right_mul S k (a 0) (a 0).property f hf
    have h1 := strip_right_mul S k (a 1) (a 1).property (f*S.t) hft
    simpa [rightEval, mul_add, mul_assoc] using strip_add_mem S k h0 h1
  · intro hf
    exact ⟨by simpa using strip_left_mul S k f hf 1 (one_mem_strip S k),
      strip_left_mul S k f hf S.t (variable_mem_strip S k)⟩

def stripCoeffs (S : FlagSystem D) (k : ℕ) (z : D) (hz : z ∈ strip S k) :
    Fin 2 → S.H (k+1) := Classical.choose hz

theorem stripCoeffs_eval (S : FlagSystem D) (k : ℕ) (z : D) (hz : z ∈ strip S k) :
    rightEval (S.H (k+1)).subtype S.t (stripCoeffs S k z hz) = z :=
  Classical.choose_spec hz

def firstColumn (S : FlagSystem D) (k : ℕ) (f : S.H k) : Fin 2 → S.H (k+1) :=
  stripCoeffs S k f ((strip_pair_criterion S k f).mpr f.property).1

def secondColumn (S : FlagSystem D) (k : ℕ) (f : S.H k) : Fin 2 → S.H (k+1) :=
  stripCoeffs S k ((f : D)*S.t) ((strip_pair_criterion S k f).mpr f.property).2

theorem firstColumn_eval (S : FlagSystem D) (k : ℕ) (f : S.H k) :
    rightEval (S.H (k+1)).subtype S.t (firstColumn S k f) = (f : D) :=
  stripCoeffs_eval S k f _

theorem secondColumn_eval (S : FlagSystem D) (k : ℕ) (f : S.H k) :
    rightEval (S.H (k+1)).subtype S.t (secondColumn S k f) = (f : D)*S.t :=
  stripCoeffs_eval S k ((f : D)*S.t) _

def reciprocalValue (S : FlagSystem D) (k : ℕ) (f : S.H k) : D :=
  (secondColumn S k f 1 : D)-(firstColumn S k f 1 : D)*S.t

theorem reciprocalValue_of_expansions (S : FlagSystem D) (k : ℕ) (f : S.H k)
    (a b c d : S.H (k+1))
    (hf : (a : D)+S.t*b = f) (hft : (c : D)+S.t*d = (f : D)*S.t) :
    reciprocalValue S k f = (d : D)-(b : D)*S.t := by
  have h0 : firstColumn S k f = ![a,b] := by
    apply strip_right_injective S k
    exact (firstColumn_eval S k f).trans (by simpa [rightEval] using hf.symm)
  have h1 : secondColumn S k f = ![c,d] := by
    apply strip_right_injective S k
    exact (secondColumn_eval S k f).trans (by simpa [rightEval] using hft.symm)
  simp [reciprocalValue, h0, h1]

theorem variable_mul_reciprocalValue (S : FlagSystem D) (k : ℕ) (f : S.H k) :
    S.t*reciprocalValue S k f = (firstColumn S k f 0 : D)*S.t-
      (secondColumn S k f 0 : D) := by
  have h0 := firstColumn_eval S k f
  have h1 := secondColumn_eval S k f
  simp only [rightEval, Subfield.subtype_apply] at h0 h1
  unfold reciprocalValue
  rw [← h0] at h1
  calc
    _ = S.t*(secondColumn S k f 1 : D)-
        S.t*(firstColumn S k f 1 : D)*S.t := by noncomm_ring
    _ = ((firstColumn S k f 0 : D)+S.t*(firstColumn S k f 1 : D))*S.t-
        (secondColumn S k f 0 : D)-S.t*(firstColumn S k f 1 : D)*S.t := by
      rw [eq_sub_of_add_eq h1]
      abel
    _ = _ := by noncomm_ring

end

end QuantumFlags

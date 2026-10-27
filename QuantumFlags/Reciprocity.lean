import QuantumFlags.StripCoordinates

namespace QuantumFlags

noncomputable section

variable {D : Type*} [DivisionRing D]

theorem reciprocalValue_mem (S : FlagSystem D) (k : ℕ) (f : S.H k) :
    reciprocalValue S k f ∈ S.H (k+2) := by
  apply (strip_right_stabilizer S k _).mp
  intro z hz
  rw [strip_eq_left S (k+1) (by omega)] at hz ⊢
  obtain ⟨uv, rfl⟩ := hz
  let a := firstColumn S k f 0
  let b := firstColumn S k f 1
  let c := secondColumn S k f 0
  let d := secondColumn S k f 1
  refine ⟨![-uv 1*c+uv 0*d, uv 1*a-uv 0*b], ?_⟩
  have ht : S.t*reciprocalValue S k f = (a : D)*S.t-c :=
    variable_mul_reciprocalValue S k f
  calc
    leftEval (S.H (k+1)).subtype S.t ![-uv 1*c+uv 0*d, uv 1*a-uv 0*b] =
        (uv 0 : D)*((d : D)-(b : D)*S.t)+(uv 1 : D)*((a : D)*S.t-c) := by
      simp only [leftEval, Matrix.cons_val_zero, Matrix.cons_val_one,
        Subfield.subtype_apply, Subfield.coe_add, Subfield.coe_sub,
        Subfield.coe_neg, Subfield.coe_mul]
      noncomm_ring
    _ = (uv 0 : D)*reciprocalValue S k f+(uv 1 : D)*(S.t*reciprocalValue S k f) := by
      rw [ht]; rfl
    _ = leftEval (S.H (k+1)).subtype S.t uv*reciprocalValue S k f := by
      simp only [leftEval, Subfield.subtype_apply]
      noncomm_ring

theorem reciprocalValue_one (S : FlagSystem D) (k : ℕ) :
    reciprocalValue S k 1 = 1 := by
  have h := reciprocalValue_of_expansions S k 1 1 0 0 1 (by simp) (by simp)
  simpa using h

theorem reciprocalValue_add (S : FlagSystem D) (k : ℕ) (f g : S.H k) :
    reciprocalValue S k (f+g) = reciprocalValue S k f+reciprocalValue S k g := by
  let a := firstColumn S k f
  let b := secondColumn S k f
  let c := firstColumn S k g
  let d := secondColumn S k g
  have hf := firstColumn_eval S k f
  have hft := secondColumn_eval S k f
  have hg := firstColumn_eval S k g
  have hgt := secondColumn_eval S k g
  simp only [rightEval, Subfield.subtype_apply] at hf hft hg hgt
  have h0 : ((a 0+c 0 : S.H (k+1)) : D)+S.t*(a 1+c 1 : S.H (k+1)) =
      ((f+g : S.H k) : D) := by
    simp only [Subfield.coe_add]
    change (firstColumn S k f 0 : D)+(firstColumn S k g 0 : D)+
      S.t*((firstColumn S k f 1 : D)+(firstColumn S k g 1 : D)) = (f : D)+g
    rw [← hf, ← hg]
    noncomm_ring
  have h1 : ((b 0+d 0 : S.H (k+1)) : D)+S.t*(b 1+d 1 : S.H (k+1)) =
      (((f+g : S.H k) : D))*S.t := by
    simp only [Subfield.coe_add, add_mul]
    change (secondColumn S k f 0 : D)+(secondColumn S k g 0 : D)+
      S.t*((secondColumn S k f 1 : D)+(secondColumn S k g 1 : D)) = (f : D)*S.t+g*S.t
    rw [← hft, ← hgt]
    noncomm_ring
  rw [reciprocalValue_of_expansions S k (f+g) (a 0+c 0) (a 1+c 1)
    (b 0+d 0) (b 1+d 1) h0 h1]
  simp only [Subfield.coe_add, reciprocalValue]
  dsimp [a, b, c, d]
  noncomm_ring

theorem reciprocalValue_mul (S : FlagSystem D) (k : ℕ) (f g : S.H k) :
    reciprocalValue S k (f*g) = reciprocalValue S k f*reciprocalValue S k g := by
  let a := firstColumn S k f
  let b := secondColumn S k f
  let c := firstColumn S k g
  let d := secondColumn S k g
  have hf := firstColumn_eval S k f
  have hft := secondColumn_eval S k f
  have hg := firstColumn_eval S k g
  have hgt := secondColumn_eval S k g
  simp only [rightEval, Subfield.subtype_apply] at hf hft hg hgt
  have h0 : ((a 0*c 0+b 0*c 1 : S.H (k+1)) : D)+
      S.t*(a 1*c 0+b 1*c 1 : S.H (k+1)) = ((f*g : S.H k) : D) := by
    simp only [Subfield.coe_add, Subfield.coe_mul]
    change (firstColumn S k f 0 : D)*(firstColumn S k g 0 : D)+
      (secondColumn S k f 0 : D)*(firstColumn S k g 1 : D)+
      S.t*((firstColumn S k f 1 : D)*(firstColumn S k g 0 : D)+
        (secondColumn S k f 1 : D)*(firstColumn S k g 1 : D)) = (f : D)*g
    calc
      _ = ((firstColumn S k f 0 : D)+S.t*(firstColumn S k f 1 : D))*
          (firstColumn S k g 0 : D)+
          ((secondColumn S k f 0 : D)+S.t*(secondColumn S k f 1 : D))*
          (firstColumn S k g 1 : D) := by noncomm_ring
      _ = (f : D)*(firstColumn S k g 0 : D)+
          ((f : D)*S.t)*(firstColumn S k g 1 : D) := by rw [hf, hft]
      _ = (f : D)*((firstColumn S k g 0 : D)+S.t*(firstColumn S k g 1 : D)) := by
        noncomm_ring
      _ = _ := by rw [hg]
  have h1 : ((a 0*d 0+b 0*d 1 : S.H (k+1)) : D)+
      S.t*(a 1*d 0+b 1*d 1 : S.H (k+1)) = ((f*g : S.H k) : D)*S.t := by
    simp only [Subfield.coe_add, Subfield.coe_mul]
    change (firstColumn S k f 0 : D)*(secondColumn S k g 0 : D)+
      (secondColumn S k f 0 : D)*(secondColumn S k g 1 : D)+
      S.t*((firstColumn S k f 1 : D)*(secondColumn S k g 0 : D)+
        (secondColumn S k f 1 : D)*(secondColumn S k g 1 : D)) = ((f : D)*g)*S.t
    calc
      _ = ((firstColumn S k f 0 : D)+S.t*(firstColumn S k f 1 : D))*
          (secondColumn S k g 0 : D)+
          ((secondColumn S k f 0 : D)+S.t*(secondColumn S k f 1 : D))*
          (secondColumn S k g 1 : D) := by noncomm_ring
      _ = (f : D)*(secondColumn S k g 0 : D)+
          ((f : D)*S.t)*(secondColumn S k g 1 : D) := by rw [hf, hft]
      _ = (f : D)*((secondColumn S k g 0 : D)+S.t*(secondColumn S k g 1 : D)) := by
        noncomm_ring
      _ = _ := by rw [hgt, mul_assoc]
  rw [reciprocalValue_of_expansions S k (f*g)
    (a 0*c 0+b 0*c 1) (a 1*c 0+b 1*c 1)
    (a 0*d 0+b 0*d 1) (a 1*d 0+b 1*d 1) h0 h1]
  have ht := variable_mul_reciprocalValue S k g
  change S.t*reciprocalValue S k g = (c 0 : D)*S.t-d 0 at ht
  simp only [Subfield.coe_add, Subfield.coe_mul]
  change (a 1 : D)*d 0+(b 1 : D)*d 1-
    ((a 1 : D)*c 0+(b 1 : D)*c 1)*S.t =
    ((b 1 : D)-(a 1 : D)*S.t)*reciprocalValue S k g
  calc
    _ = (b 1 : D)*((d 1 : D)-(c 1 : D)*S.t)-
        (a 1 : D)*((c 0 : D)*S.t-d 0) := by noncomm_ring
    _ = (b 1 : D)*reciprocalValue S k g-(a 1 : D)*(S.t*reciprocalValue S k g) := by
      rw [ht]; rfl
    _ = _ := by noncomm_ring

def reciprocalHom (S : FlagSystem D) (k : ℕ) : S.H k →+* S.H (k+2) where
  toFun f := ⟨reciprocalValue S k f, reciprocalValue_mem S k f⟩
  map_one' := Subtype.ext (reciprocalValue_one S k)
  map_mul' f g := Subtype.ext (reciprocalValue_mul S k f g)
  map_zero' := by
    apply Subtype.ext
    have h := reciprocalValue_of_expansions S k 0 0 0 0 0 (by simp) (by simp)
    simpa using h
  map_add' f g := Subtype.ext (reciprocalValue_add S k f g)

theorem reciprocalHom_surjective (S : FlagSystem D) (k : ℕ) :
    Function.Surjective (reciprocalHom S k) := by
  intro g
  have hg : (g : D) ∈ strip S (k+1) := by
    simpa using strip_right_mul S (k+1) g g.property 1 (one_mem_strip S (k+1))
  have htg := strip_right_mul S (k+1) g g.property S.t (variable_mem_strip S (k+1))
  rw [strip_eq_left S (k+1) (by omega)] at hg htg
  obtain ⟨uv, huv⟩ := hg
  obtain ⟨rs, hrs⟩ := htg
  let a := rs 1
  let b := -uv 1
  let c := -rs 0
  let d := uv 0
  have he0 : (d : D)-(b : D)*S.t = g := by
    simpa [leftEval, b, d] using huv
  have he1 : (a : D)*S.t-c = S.t*(g : D) := by
    simpa [leftEval, a, c, add_comm] using hrs
  let f : D := (a : D)+S.t*b
  have hft : f*S.t = (c : D)+S.t*d := by
    dsimp [f]
    rw [← he0] at he1
    have htd : S.t*(d : D) = (a : D)*S.t-(c : D)+S.t*(b : D)*S.t := by
      have hh := congrArg (fun x : D => x+S.t*(b : D)*S.t) he1.symm
      simpa only [mul_sub, mul_assoc, sub_add_cancel] using hh
    rw [add_mul, htd]
    noncomm_ring
  have hfm : f ∈ S.H k := by
    apply (strip_pair_criterion S k f).mp
    exact ⟨⟨![a,b], rfl⟩, ⟨![c,d], by simpa [rightEval] using hft.symm⟩⟩
  refine ⟨⟨f,hfm⟩, ?_⟩
  apply Subtype.ext
  exact (reciprocalValue_of_expansions S k ⟨f,hfm⟩ a b c d rfl hft.symm).trans he0

def reciprocalEquiv (S : FlagSystem D) (k : ℕ) : S.H k ≃+* S.H (k+2) :=
  RingEquiv.ofBijective (reciprocalHom S k)
    ⟨(reciprocalHom S k).injective, reciprocalHom_surjective S k⟩

theorem reciprocalEquiv_formula (S : FlagSystem D) (k : ℕ) (f : S.H k) :
    (reciprocalEquiv S k f : D) = (secondColumn S k f 1 : D)-
      (firstColumn S k f 1 : D)*S.t := rfl

theorem actual_reciprocal_isomorphism (k : ℕ) :
    Nonempty (imageField actualQuantumChain k ≃+* imageField actualQuantumChain (k+2)) :=
  ⟨reciprocalEquiv actualFlagSystem k⟩

end

end QuantumFlags

import QuantumFlags.SkewExtension

namespace QuantumFlags

noncomputable section

variable {K : Type*} [DivisionRing K] [MulSemiringAction (Multiplicative ℕ) K]

theorem skew_coeff_mul_constant (p : SkewPolynomial K) (a : K) (n : ℕ) :
    SkewPolynomial.coeff (p*SkewPolynomial.C a) n =
      SkewPolynomial.coeff p n*(SkewPolynomial.φ^[n]) a := by
  by_cases ha : a = 0
  · simp [ha]
  rw [skew_coeff_mul_expansion,SkewPolynomial.support_C ha]
  simp only [Finset.sum_singleton,SkewPolynomial.coeff_C_zero,Nat.add_zero]
  rw [Finset.sum_eq_single n]
  · simp
  · intro i _ hi
    simp [hi]
  · intro hn
    rw [SkewPolynomial.notMem_support_iff.mp hn,zero_mul]
    simp

instance skewPolynomialRightModule : Module Kᵐᵒᵖ (SkewPolynomial K) :=
  Module.compHom (SkewPolynomial K) SkewPolynomial.CRingHom.op

def boundedSkewRight (m : ℕ) : Submodule Kᵐᵒᵖ (SkewPolynomial K) where
  carrier := {p | ∀ k, m < k → SkewPolynomial.coeff p k = 0}
  zero_mem' := by simp
  add_mem' hp hq k hk := by rw [SkewPolynomial.coeff_add,hp k hk,hq k hk,add_zero]
  smul_mem' a p hp k hk := by
    change SkewPolynomial.coeff (p*SkewPolynomial.C a.unop) k = 0
    rw [skew_coeff_mul_constant,hp k hk,zero_mul]

theorem skew_phi_iterate_eq_aut (σ : K ≃+* K) (hσ : ∀ a : K, SkewPolynomial.φ a = σ a)
    (n : ℕ) (a : K) : (SkewPolynomial.φ^[n]) a = (σ^n) a := by
  have hf : (SkewPolynomial.φ : K → K) = σ := funext hσ
  rw [hf,← RingAut.coe_pow]

def skewRightOfCoefficients (σ : K ≃+* K) (m : ℕ) (c : Fin (m+1) → Kᵐᵒᵖ) :
    SkewPolynomial K := skewOfCoefficients m (fun i => (σ^i.val) (c i).unop)

def boundedSkewRightEquiv (σ : K ≃+* K) (hσ : ∀ a : K, SkewPolynomial.φ a = σ a)
    (m : ℕ) : boundedSkewRight (K := K) m ≃ₗ[Kᵐᵒᵖ] (Fin (m+1) → Kᵐᵒᵖ) where
  toFun p i := MulOpposite.op ((σ^i.val).symm (SkewPolynomial.coeff (p : SkewPolynomial K) i.val))
  invFun c := ⟨skewRightOfCoefficients σ m c,skewOfCoefficients_coeff_above m _⟩
  left_inv p := by
    apply Subtype.ext
    apply skew_ext
    intro k
    by_cases hk : k ≤ m
    · change SkewPolynomial.coeff
        (skewOfCoefficients m (fun i => (σ^i.val)
          ((σ^i.val).symm (SkewPolynomial.coeff (p : SkewPolynomial K) i.val)))) k =
          SkewPolynomial.coeff (p : SkewPolynomial K) k
      rw [skewOfCoefficients_coeff_le m _ k hk]
      exact (σ^k).apply_symm_apply _
    · rw [show SkewPolynomial.coeff (skewRightOfCoefficients σ m _ ) k = 0 from
        skewOfCoefficients_coeff_above m _ k (Nat.lt_of_not_ge hk),
        p.property k (Nat.lt_of_not_ge hk)]
  right_inv c := by
    funext i
    change MulOpposite.op ((σ^i.val).symm
      (SkewPolynomial.coeff (skewOfCoefficients m (fun j => (σ^j.val) (c j).unop)) i.val)) = c i
    rw [skewOfCoefficients_coeff_le m _ i.val (Nat.le_of_lt_succ i.isLt),
      RingEquiv.symm_apply_apply,MulOpposite.op_unop]
  map_add' p q := by
    funext i
    change MulOpposite.op ((σ^i.val).symm (SkewPolynomial.coeff
      ((p : SkewPolynomial K)+(q : SkewPolynomial K)) i.val)) = _
    rw [SkewPolynomial.coeff_add,map_add,MulOpposite.op_add]
    rfl
  map_smul' a p := by
    funext i
    change MulOpposite.op ((σ^i.val).symm (SkewPolynomial.coeff
      ((p : SkewPolynomial K)*SkewPolynomial.C a.unop) i.val)) =
        a*MulOpposite.op ((σ^i.val).symm (SkewPolynomial.coeff (p : SkewPolynomial K) i.val))
    rw [skew_coeff_mul_constant,skew_phi_iterate_eq_aut σ hσ,map_mul,RingEquiv.symm_apply_apply,
      MulOpposite.op_mul,MulOpposite.op_unop]

theorem boundedSkewRight_finite (σ : K ≃+* K) (hσ : ∀ a : K, SkewPolynomial.φ a = σ a) (m : ℕ) :
    FiniteDimensional Kᵐᵒᵖ (boundedSkewRight (K := K) m) :=
  FiniteDimensional.of_injective (boundedSkewRightEquiv σ hσ m).toLinearMap
    (boundedSkewRightEquiv σ hσ m).injective

theorem boundedSkewRight_finrank (σ : K ≃+* K) (hσ : ∀ a : K, SkewPolynomial.φ a = σ a) (m : ℕ) :
    Module.finrank Kᵐᵒᵖ (boundedSkewRight (K := K) m) = m+1 := by
  simpa using (boundedSkewRightEquiv σ hσ m).finrank_eq

theorem boundedSkewRight_product (m n : ℕ) (p : boundedSkewRight (K := K) m)
    (q : boundedSkewRight (K := K) n) :
    (p : SkewPolynomial K)*(q : SkewPolynomial K) ∈ boundedSkewRight (m+n) := by
  intro k hk
  apply skew_product_bounded _ _ m n ?_ ?_ k hk
  · intro i hi
    by_contra h
    exact (SkewPolynomial.mem_support_iff.mp hi) (p.property i (Nat.lt_of_not_ge h))
  · intro i hi
    by_contra h
    exact (SkewPolynomial.mem_support_iff.mp hi) (q.property i (Nat.lt_of_not_ge h))

def skewRightRelation (m : ℕ) (p q : boundedSkewRight (K := K) m) :
    (boundedSkewRight (K := K) m × boundedSkewRight (K := K) m) →ₗ[Kᵐᵒᵖ]
      boundedSkewRight (K := K) (m+m) where
  toFun w := ⟨(p : SkewPolynomial K)*(w.1 : SkewPolynomial K)-
      (q : SkewPolynomial K)*(w.2 : SkewPolynomial K),
    (boundedSkewRight (K := K) (m+m)).sub_mem (boundedSkewRight_product m m p w.1)
      (boundedSkewRight_product m m q w.2)⟩
  map_add' w z := by
    apply Subtype.ext
    change (p : SkewPolynomial K)*((w.1 : SkewPolynomial K)+(z.1 : SkewPolynomial K))-
      (q : SkewPolynomial K)*((w.2 : SkewPolynomial K)+(z.2 : SkewPolynomial K)) =
      ((p : SkewPolynomial K)*(w.1 : SkewPolynomial K)-(q : SkewPolynomial K)*(w.2 : SkewPolynomial K))+
      ((p : SkewPolynomial K)*(z.1 : SkewPolynomial K)-(q : SkewPolynomial K)*(z.2 : SkewPolynomial K))
    noncomm_ring
  map_smul' a w := by
    apply Subtype.ext
    change (p : SkewPolynomial K)*((w.1 : SkewPolynomial K)*SkewPolynomial.C a.unop)-
      (q : SkewPolynomial K)*((w.2 : SkewPolynomial K)*SkewPolynomial.C a.unop) =
      ((p : SkewPolynomial K)*(w.1 : SkewPolynomial K)-
        (q : SkewPolynomial K)*(w.2 : SkewPolynomial K))*SkewPolynomial.C a.unop
    noncomm_ring

theorem skew_common_right_multiple (σ : K ≃+* K) (hσ : ∀ a : K, SkewPolynomial.φ a = σ a)
    (p q : SkewPolynomial K) (hp : p ≠ 0) (hq : q ≠ 0) :
    ∃ X Y : SkewPolynomial K, X ≠ 0 ∧ Y ≠ 0 ∧ p*X=q*Y := by
  let m := max (skewNatDegree p) (skewNatDegree q)
  let p' : boundedSkewRight (K := K) m := ⟨p,fun k hk => skew_coeff_above_degree p k
    (lt_of_le_of_lt (le_max_left _ _) hk)⟩
  let q' : boundedSkewRight (K := K) m := ⟨q,fun k hk => skew_coeff_above_degree q k
    (lt_of_le_of_lt (le_max_right _ _) hk)⟩
  letI := boundedSkewRight_finite σ hσ m
  letI := boundedSkewRight_finite σ hσ (m+m)
  let f := skewRightRelation m p' q'
  have hd : Module.finrank Kᵐᵒᵖ (boundedSkewRight (K := K) (m+m)) <
      Module.finrank Kᵐᵒᵖ (boundedSkewRight (K := K) m × boundedSkewRight (K := K) m) := by
    rw [Module.finrank_prod,boundedSkewRight_finrank σ hσ,boundedSkewRight_finrank σ hσ]
    omega
  have hker : LinearMap.ker f ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hd
  obtain ⟨w,hw,hwnz⟩ := (LinearMap.ker f).ne_bot_iff.mp hker
  have heq : p*(w.1 : SkewPolynomial K) = q*(w.2 : SkewPolynomial K) := by
    have he := congrArg (fun a : boundedSkewRight (K := K) (m+m) => (a : SkewPolynomial K))
      (LinearMap.mem_ker.mp hw)
    change p*(w.1 : SkewPolynomial K)-q*(w.2 : SkewPolynomial K) = 0 at he
    exact sub_eq_zero.mp he
  have hx : (w.1 : SkewPolynomial K) ≠ 0 := by
    intro h
    have hy : (w.2 : SkewPolynomial K) = 0 :=
      (mul_eq_zero.mp (by rw [← heq,h,mul_zero])).resolve_left hq
    exact hwnz (Prod.ext (Subtype.ext h) (Subtype.ext hy))
  have hy : (w.2 : SkewPolynomial K) ≠ 0 := by
    intro h
    have hx' : (w.1 : SkewPolynomial K) = 0 :=
      (mul_eq_zero.mp (by rw [heq,h,mul_zero])).resolve_left hp
    exact hx hx'
  exact ⟨w.1,w.2,hx,hy,heq⟩


omit [MulSemiringAction (Multiplicative ℕ) K] in
theorem automorphism_skew_two_sided_ore (τ : K ≃+* K) :
    letI := automorphismAction τ
    ∀ p q : SkewPolynomial K, p ≠ 0 → q ≠ 0 →
      (∃ X Y : SkewPolynomial K, X ≠ 0 ∧ Y ≠ 0 ∧ X*p=Y*q) ∧
      (∃ X Y : SkewPolynomial K, X ≠ 0 ∧ Y ≠ 0 ∧ p*X=q*Y) := by
  letI := automorphismAction τ
  intro p q hp hq
  exact ⟨skew_common_left_multiple p q hp hq,
    skew_common_right_multiple τ (automorphismAction_phi τ) p q hp hq⟩

end

end QuantumFlags

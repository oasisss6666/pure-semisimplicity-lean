import QuantumFlags.SkewEvaluation

namespace QuantumFlags

noncomputable section

open scoped nonZeroDivisors

variable {K L : Type*} [DivisionRing K] [MulSemiringAction (Multiplicative ℕ) K] [DivisionRing L]

def skewDenominatorUnits (f : SkewPolynomial K →+* L) (hf : Function.Injective f) :
    (SkewPolynomial K)⁰ →* Lˣ where
  toFun s := Units.mk0 (f s) (by
    intro h
    apply nonZeroDivisors.coe_ne_zero s
    apply hf
    simpa only [map_zero] using h)
  map_one' := by apply Units.ext; exact map_one f
  map_mul' s t := by
    apply Units.ext
    exact map_mul f (s : SkewPolynomial K) (t : SkewPolynomial K)

def skewLift (f : SkewPolynomial K →+* L) (hf : Function.Injective f) :
    SkewFractions K →+* L :=
  OreLocalization.universalHom f (skewDenominatorUnits f hf) (fun _ => rfl)

theorem skewLift_numerator (f : SkewPolynomial K →+* L) (hf : Function.Injective f)
    (p : SkewPolynomial K) : skewLift f hf (skewNumerator p) = f p :=
  OreLocalization.universalHom_commutes f (skewDenominatorUnits f hf) (fun _ => rfl)

theorem skew_fractionHom_ext (f g : SkewFractions K →+* L)
    (h : ∀ p : SkewPolynomial K, f (skewNumerator p) = g (skewNumerator p)) : f = g := by
  let b := f.comp (skewNumerator (K := K))
  have hb : Function.Injective b := f.injective.comp skewNumerator_injective
  let u := skewDenominatorUnits b hb
  exact (OreLocalization.universalHom_unique b u (fun _ => rfl) f (fun _ => rfl)).trans
    (OreLocalization.universalHom_unique b u (fun _ => rfl) g (fun p => (h p).symm)).symm

def skewAutoHom (e : SkewPolynomial K ≃+* SkewPolynomial K) :
    SkewFractions K →+* SkewFractions K :=
  skewLift ((skewNumerator (K := K)).comp e.toRingHom)
    (skewNumerator_injective.comp e.injective)

theorem skewAutoHom_numerator (e : SkewPolynomial K ≃+* SkewPolynomial K)
    (p : SkewPolynomial K) : skewAutoHom e (skewNumerator p) = skewNumerator (e p) :=
  skewLift_numerator _ _ p

theorem skewAutoHom_inverse_left (e : SkewPolynomial K ≃+* SkewPolynomial K) :
    (skewAutoHom e.symm).comp (skewAutoHom e) = RingHom.id (SkewFractions K) := by
  apply skew_fractionHom_ext
  intro p
  simp only [RingHom.comp_apply, skewAutoHom_numerator, RingEquiv.symm_apply_apply,
    RingHom.id_apply]

def extendSkewAut (e : SkewPolynomial K ≃+* SkewPolynomial K) :
    SkewFractions K ≃+* SkewFractions K where
  __ := skewAutoHom e
  invFun := skewAutoHom e.symm
  left_inv x := DFunLike.congr_fun (skewAutoHom_inverse_left e) x
  right_inv x := DFunLike.congr_fun (skewAutoHom_inverse_left e.symm) x

theorem extendSkewAut_numerator (e : SkewPolynomial K ≃+* SkewPolynomial K)
    (p : SkewPolynomial K) : extendSkewAut e (skewNumerator p) = skewNumerator (e p) :=
  skewAutoHom_numerator e p

def fractionScalingAut (c : K) (hc : ∀ a : K, Commute c a) (hcnz : c ≠ 0) :
    SkewFractions K ≃+* SkewFractions K :=
  extendSkewAut (skewScalingAut c hc hcnz)

theorem fractionScalingAut_constants (c : K) (hc : ∀ a : K, Commute c a)
    (hcnz : c ≠ 0) (a : K) :
    fractionScalingAut c hc hcnz (skewConstants a) = skewConstants a := by
  change extendSkewAut (skewScalingAut c hc hcnz) (skewNumerator (SkewPolynomial.C a)) = _
  rw [extendSkewAut_numerator, skewScalingAut_C]
  rfl

theorem fractionScalingAut_variable (c : K) (hc : ∀ a : K, Commute c a) (hcnz : c ≠ 0) :
    fractionScalingAut c hc hcnz (skewVariable (K := K)) = skewConstants c*skewVariable := by
  change extendSkewAut (skewScalingAut c hc hcnz) (skewNumerator SkewPolynomial.X) = _
  rw [extendSkewAut_numerator, skewScalingAut_X, map_mul]
  rfl

end

end QuantumFlags

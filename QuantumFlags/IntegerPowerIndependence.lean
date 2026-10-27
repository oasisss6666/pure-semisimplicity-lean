import QuantumFlags.SkewExtension
import Mathlib.LinearAlgebra.LinearIndependent.Basic

namespace QuantumFlags

noncomputable section

theorem linearIndependent_nat_of_prefix {R : Type*} {V : Type*} [Ring R] [AddCommGroup V]
    [Module R V] (v : ℕ → V) (h : ∀ r, LinearIndependent R (fun i : Fin (r+1) => v i.val)) :
    LinearIndependent R v := by
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  let m := s.sup id
  let f : s → Fin (m+1) := fun i => ⟨i.val,Nat.lt_succ_of_le (Finset.le_sup (f := id) i.property)⟩
  have hf : Function.Injective f := by
    intro i j he
    apply Subtype.ext
    exact congrArg (fun a : Fin (m+1) => a.val) he
  exact (h m).comp f hf

theorem linearIndependent_int_of_nat_shifts {R : Type*} {V : Type*} [Ring R] [AddCommGroup V]
    [Module R V] (v : ℤ → V) (hn : LinearIndependent R (fun n : ℕ => v (n : ℤ)))
    (T : ℕ → V →ₗ[R] V) (hT : ∀ m i, T m (v i) = v (i+(m : ℤ))) : LinearIndependent R v := by
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  let m := s.sup Int.natAbs
  have hge (i : s) : 0 ≤ i.val+(m : ℤ) := by
    have ha : i.val.natAbs ≤ m := Finset.le_sup (f := Int.natAbs) i.property
    have hac : (i.val.natAbs : ℤ) ≤ (m : ℤ) := Int.ofNat_le.mpr ha
    have hneg : -i.val ≤ (i.val.natAbs : ℤ) := by
      simpa using (Int.le_natAbs (a := -i.val))
    omega
  let f : s → ℕ := fun i => (i.val+(m : ℤ)).toNat
  have hf : Function.Injective f := by
    intro i j he
    apply Subtype.ext
    have hi := Int.toNat_of_nonneg (hge i)
    have hj := Int.toNat_of_nonneg (hge j)
    have hc := congrArg (fun n : ℕ => (n : ℤ)) he
    change ((i.val+(m : ℤ)).toNat : ℤ) = ((j.val+(m : ℤ)).toNat : ℤ) at hc
    omega
  apply LinearIndependent.of_comp (T m)
  have he : (T m) ∘ (fun i : s => v i.val) = fun i : s => v (f i : ℤ) := by
    funext i
    change T m (v i.val) = v ((i.val+(m : ℤ)).toNat : ℤ)
    rw [hT,Int.toNat_of_nonneg (hge i)]
  change LinearIndependent R ((T m) ∘ (fun i : s => v i.val))
  rw [he]
  exact hn.comp f hf

variable {E : Type*} {D : Type*} [DivisionRing E] [DivisionRing D]

@[instance_reducible]
def powerLeftCoefficientModule (ι : E →+* D) : Module E D := Module.compHom D ι

@[instance_reducible]
def powerRightCoefficientModule (ι : E →+* D) : Module Eᵐᵒᵖ D := Module.compHom D ι.op

theorem powerLeftCoefficient_smul (ι : E →+* D) (a : E) (x : D) :
    letI := powerLeftCoefficientModule ι
    a • x = ι a*x := rfl

theorem powerRightCoefficient_smul (ι : E →+* D) (a : Eᵐᵒᵖ) (x : D) :
    letI := powerRightCoefficientModule ι
    a • x = x*ι a.unop := rfl

def rightMultiplyOverLeftCoefficients (ι : E →+* D) (c : D) :
    letI := powerLeftCoefficientModule ι
    D →ₗ[E] D := by
  letI := powerLeftCoefficientModule ι
  exact {
    toFun x := x*c
    map_add' x y := add_mul x y c
    map_smul' a x := by
      change (ι a*x)*c = ι a*(x*c)
      exact mul_assoc _ _ _ }

def leftMultiplyOverRightCoefficients (ι : E →+* D) (c : D) :
    letI := powerRightCoefficientModule ι
    D →ₗ[Eᵐᵒᵖ] D := by
  letI := powerRightCoefficientModule ι
  exact {
    toFun x := c*x
    map_add' x y := mul_add c x y
    map_smul' a x := by
      change c*(x*ι a.unop) = (c*x)*ι a.unop
      exact (mul_assoc _ _ _).symm }

theorem integer_left_powers_linearIndependent (ι : E →+* D) (v : D) (hv : v ≠ 0)
    (h : ∀ r, Function.Injective (fun c : Fin (r+1) → E => ∑ i, ι (c i)*v^i.val)) :
    letI := powerLeftCoefficientModule ι
    LinearIndependent E (fun i : ℤ => v^i) := by
  letI := powerLeftCoefficientModule ι
  have hprefix (r : ℕ) : LinearIndependent E (fun i : Fin (r+1) => v^i.val) := by
    apply linearIndependent_iff_injective_fintypeLinearCombination.mpr
    intro c d he
    apply h r
    change (∑ i,ι (c i)*v^i.val) = (∑ i,ι (d i)*v^i.val)
    simpa only [Fintype.linearCombination_apply,powerLeftCoefficient_smul] using he
  have hn := linearIndependent_nat_of_prefix (fun n : ℕ => v^n) hprefix
  apply linearIndependent_int_of_nat_shifts (fun i : ℤ => v^i) (by simpa using hn)
    (fun m => rightMultiplyOverLeftCoefficients ι (v^m))
  intro m i
  change v^i*v^m = v^(i+(m : ℤ))
  rw [zpow_add₀ hv,zpow_natCast]

theorem integer_right_powers_linearIndependent (ι : E →+* D) (v : D) (hv : v ≠ 0)
    (h : ∀ r, Function.Injective (fun c : Fin (r+1) → E => ∑ i,v^i.val*ι (c i))) :
    letI := powerRightCoefficientModule ι
    LinearIndependent Eᵐᵒᵖ (fun i : ℤ => v^i) := by
  letI := powerRightCoefficientModule ι
  have hprefix (r : ℕ) : LinearIndependent Eᵐᵒᵖ (fun i : Fin (r+1) => v^i.val) := by
    apply linearIndependent_iff_injective_fintypeLinearCombination.mpr
    intro c d he
    have hc : (fun i => (c i).unop) = (fun i => (d i).unop) := by
      apply h r
      change (∑ i,v^i.val*ι (c i).unop) = (∑ i,v^i.val*ι (d i).unop)
      simpa only [Fintype.linearCombination_apply,powerRightCoefficient_smul] using he
    funext i
    exact MulOpposite.unop_injective (congrFun hc i)
  have hn := linearIndependent_nat_of_prefix (fun n : ℕ => v^n) hprefix
  apply linearIndependent_int_of_nat_shifts (fun i : ℤ => v^i) (by simpa using hn)
    (fun m => leftMultiplyOverRightCoefficients ι (v^m))
  intro m i
  change v^m*v^i = v^(i+(m : ℤ))
  rw [add_comm i,zpow_add₀ hv,zpow_natCast]

variable {K : Type*} [DivisionRing K]

theorem extension_variable_ne_zero (τ : K ≃+* K) : extensionVariable τ ≠ 0 := by
  intro hv
  let c : Fin (1+1) → K := ![0,1]
  let d : Fin (1+1) → K := 0
  have he : c = d := (extension_left_powers_independent τ 1) (by
    simp [c,d,Fin.sum_univ_two,hv])
  have hz : (1 : K) = 0 := by simpa [c,d] using congrFun he 1
  exact one_ne_zero hz

theorem extension_integer_left_powers_independent (τ : K ≃+* K) :
    letI := powerLeftCoefficientModule (extensionConstants τ)
    LinearIndependent K (fun i : ℤ => extensionVariable τ ^ i) :=
  integer_left_powers_linearIndependent (extensionConstants τ) (extensionVariable τ)
    (extension_variable_ne_zero τ) (extension_left_powers_independent τ)

theorem extension_integer_right_powers_independent (τ : K ≃+* K) :
    letI := powerRightCoefficientModule (extensionConstants τ)
    LinearIndependent Kᵐᵒᵖ (fun i : ℤ => extensionVariable τ ^ i) :=
  integer_right_powers_linearIndependent (extensionConstants τ) (extensionVariable τ)
    (extension_variable_ne_zero τ) (extension_right_powers_independent τ)

end

end QuantumFlags

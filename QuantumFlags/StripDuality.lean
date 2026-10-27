import QuantumFlags.StripModules
import QuantumFlags.Reciprocity

namespace QuantumFlags

noncomputable section

variable {K : Type*} [DivisionRing K]

def pairFunctional (u v : K) : (Fin 2 → K) →ₗ[Kᵐᵒᵖ] K where
  toFun x := -v*x 0+u*x 1
  map_add' x y := by
    simp only [Pi.add_apply]
    noncomm_ring
  map_smul' r x := by
    change -v*(x 0*r.unop)+u*(x 1*r.unop) = (-v*x 0+u*x 1)*r.unop
    noncomm_ring

def pairDualLinear : (Fin 2 → K) →ₗ[K] ((Fin 2 → K) →ₗ[Kᵐᵒᵖ] K) where
  toFun c := pairFunctional (c 0) (c 1)
  map_add' c d := by
    apply LinearMap.ext
    intro x
    change -(c 1+d 1)*x 0+(c 0+d 0)*x 1 =
      (-c 1*x 0+c 0*x 1)+(-d 1*x 0+d 0*x 1)
    noncomm_ring
  map_smul' r c := by
    apply LinearMap.ext
    intro x
    change -(r*c 1)*x 0+(r*c 0)*x 1 = r*(-c 1*x 0+c 0*x 1)
    noncomm_ring

theorem pairDualLinear_bijective : Function.Bijective (pairDualLinear (K := K)) := by
  constructor
  · intro c d h
    have h0 : c 0 = d 0 := by
      simpa [pairDualLinear, pairFunctional] using
        congrArg (fun l : (Fin 2 → K) →ₗ[Kᵐᵒᵖ] K => l ![0,1]) h
    have h1 : c 1 = d 1 := by
      simpa [pairDualLinear, pairFunctional] using
        congrArg (fun l : (Fin 2 → K) →ₗ[Kᵐᵒᵖ] K => l ![1,0]) h
    funext i
    fin_cases i
    · exact h0
    · exact h1
  · intro l
    refine ⟨![l ![0,1], -l ![1,0]], ?_⟩
    apply LinearMap.ext
    intro x
    have hx : x = MulOpposite.op (x 0) • (![1,0] : Fin 2 → K)+
        MulOpposite.op (x 1) • (![0,1] : Fin 2 → K) := by
      ext i
      fin_cases i <;> simp [MulOpposite.smul_eq_mul_unop]
    have he := congrArg l hx
    rw [map_add, map_smul, map_smul] at he
    change l x = l ![1,0]*x 0+l ![0,1]*x 1 at he
    simpa [pairDualLinear, pairFunctional] using he.symm

def pairDualEquiv : (Fin 2 → K) ≃ₗ[K] ((Fin 2 → K) →ₗ[Kᵐᵒᵖ] K) :=
  LinearEquiv.ofBijective pairDualLinear pairDualLinear_bijective

variable {D : Type*} [DivisionRing D]

abbrev StripRightDual (S : FlagSystem D) (k : ℕ) :=
  StripSpace S k →ₗ[(S.H (k+1))ᵐᵒᵖ] S.H (k+1)

/-- The actual right-linear Hom dual in Proposition 4.3. -/
def stripDualEquiv (S : FlagSystem D) (k : ℕ) :
    StripSpace S (k+1) ≃ₗ[S.H (k+1)] StripRightDual S k :=
  ((leftStripEquiv S k).symm.trans pairDualEquiv).trans
    (LinearEquiv.congrLeft (S.H (k+1)) (S.H (k+1)) (rightStripEquiv S k))

theorem stripDualEquiv_formula (S : FlagSystem D) (k : ℕ)
    (uv ab : Fin 2 → S.H (k+1)) :
    stripDualEquiv S k (leftStripEquiv S k uv) (rightStripEquiv S k ab) =
      -uv 1*ab 0+uv 0*ab 1 := by
  simp [stripDualEquiv, pairDualEquiv, pairDualLinear, pairFunctional,
    LinearEquiv.congrLeft]

end

end QuantumFlags

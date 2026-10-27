import QuantumFlags.HomRepresentations

namespace QuantumFlags

noncomputable section

universe u

def rightHomCongr (N : DivisionBimodule.{u}) {Y : Type*} {Z : Type*} [AddCommGroup Y]
    [Module N.RightRingᵐᵒᵖ Y] [AddCommGroup Z] [Module N.RightRingᵐᵒᵖ Z]
    (e : Y ≃ₗ[N.RightRingᵐᵒᵖ] Z) :
    letI := rightHomModule N Y
    letI := rightHomModule N Z
    BimoduleRightHom N Y ≃ₗ[N.LeftRingᵐᵒᵖ] BimoduleRightHom N Z := by
  letI := rightHomModule N Y
  letI := rightHomModule N Z
  apply LinearEquiv.ofBijective (rightHomMap N e.toLinearMap)
  constructor
  · intro φ ψ h
    apply LinearMap.ext
    intro n
    apply e.injective
    exact congrArg (fun f : BimoduleRightHom N Z => f n) h
  · intro φ
    refine ⟨e.symm.toLinearMap.comp φ, ?_⟩
    apply LinearMap.ext
    intro n
    exact e.apply_symm_apply (φ n)

def rightHomPiEquiv (N : DivisionBimodule.{u}) (I : Type*) :
    letI := rightHomModule N (I → N.RightRing)
    letI := dualRightModule N
    BimoduleRightHom N (I → N.RightRing) ≃ₗ[N.LeftRingᵐᵒᵖ] (I → RightDualSpace N) := by
  letI := rightHomModule N (I → N.RightRing)
  letI := dualRightModule N
  exact {
    toFun φ i := (LinearMap.proj i).comp φ
    invFun ψ := {
      toFun n i := ψ i n
      map_add' n m := by funext i; exact (ψ i).map_add n m
      map_smul' r n := by funext i; exact (ψ i).map_smul r n }
    left_inv φ := by
      apply LinearMap.ext
      intro n
      rfl
    right_inv ψ := by
      funext i
      apply LinearMap.ext
      intro n
      rfl
    map_add' φ ψ := rfl
    map_smul' r φ := rfl }

def unopPiEquiv (K : Type u) [DivisionRing K] (I : Type*) :
    (I → Kᵐᵒᵖ) ≃ₗ[Kᵐᵒᵖ] (I → K) where
  toFun x i := (x i).unop
  invFun x i := MulOpposite.op (x i)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def homCoordinateEquiv (N : DivisionBimodule.{u}) {Y : Type*} [AddCommGroup Y]
    [Module N.RightRingᵐᵒᵖ Y] {b d : ℕ} (v : Module.Basis (Fin b) N.RightRingᵐᵒᵖ Y)
    (w : letI := dualRightModule N
      RightDualSpace N ≃ₗ[N.LeftRingᵐᵒᵖ] (Fin d → N.LeftRingᵐᵒᵖ)) :
    letI := rightHomModule N Y
    BimoduleRightHom N Y ≃ₗ[N.LeftRingᵐᵒᵖ] (Fin b → Fin d → N.LeftRingᵐᵒᵖ) := by
  letI := rightHomModule N Y
  letI := rightHomModule N (Fin b → N.RightRing)
  letI := dualRightModule N
  exact ((rightHomCongr N (v.equivFun.trans (unopPiEquiv N.RightRing (Fin b)))).trans
    (rightHomPiEquiv N (Fin b))).trans (LinearEquiv.piCongrRight (fun _ => w))

theorem hom_finrank_from_coordinates (N : DivisionBimodule.{u}) {Y : Type*} [AddCommGroup Y]
    [Module N.RightRingᵐᵒᵖ Y] {b d : ℕ} (v : Module.Basis (Fin b) N.RightRingᵐᵒᵖ Y)
    (w : letI := dualRightModule N
      RightDualSpace N ≃ₗ[N.LeftRingᵐᵒᵖ] (Fin d → N.LeftRingᵐᵒᵖ)) :
    letI := rightHomModule N Y
    Module.finrank N.LeftRingᵐᵒᵖ (BimoduleRightHom N Y) = b*d := by
  letI := rightHomModule N Y
  rw [(homCoordinateEquiv N v w).finrank_eq, Module.finrank_pi_fintype]
  simp [Module.finrank_pi]

theorem reflection_cokernel_finrank (N : DivisionBimodule.{u}) {Y : Type*} {X : Type*}
    [AddCommGroup Y] [Module N.RightRingᵐᵒᵖ Y] [AddCommGroup X]
    [Module N.LeftRingᵐᵒᵖ X] [FiniteDimensional N.LeftRingᵐᵒᵖ X] {b d : ℕ}
    (v : Module.Basis (Fin b) N.RightRingᵐᵒᵖ Y)
    (w : letI := dualRightModule N
      RightDualSpace N ≃ₗ[N.LeftRingᵐᵒᵖ] (Fin d → N.LeftRingᵐᵒᵖ))
    (β : letI := rightHomModule N Y
      X →ₗ[N.LeftRingᵐᵒᵖ] BimoduleRightHom N Y) (hβ : Function.Injective β) :
    letI := rightHomModule N Y
    Module.finrank N.LeftRingᵐᵒᵖ (BimoduleRightHom N Y ⧸ β.range) =
      b*d-Module.finrank N.LeftRingᵐᵒᵖ X := by
  letI := rightHomModule N Y
  letI : FiniteDimensional N.LeftRingᵐᵒᵖ (BimoduleRightHom N Y) :=
    FiniteDimensional.of_injective (homCoordinateEquiv N v w).toLinearMap
      (homCoordinateEquiv N v w).injective
  have he := β.range.finrank_quotient_add_finrank
  rw [hom_finrank_from_coordinates N v w, LinearMap.finrank_range_of_inj hβ] at he
  omega

end

end QuantumFlags

import QuantumFlags.BimoduleArtinian
import QuantumFlags.CornerModuleReconstruction

namespace QuantumFlags

noncomputable section

variable {D : Type*} [DivisionRing D]

def ambientTriangularRingEquiv (H : Subfield D) :
    BimoduleTriangularRing (ambientBimodule H) ≃+* TriangularRing H where
  toFun r := ⟨!![((bimoduleSourceHom (ambientBimodule H) r : H) : D),
      bimoduleCrossHom (ambientBimodule H) r;0,bimoduleTargetHom (ambientBimodule H) r],by
    change (0 : D) = 0 ∧ ((bimoduleSourceHom (ambientBimodule H) r : H) : D) ∈ H
    exact ⟨rfl,(bimoduleSourceHom (ambientBimodule H) r).property⟩⟩
  invFun r := ((triangularSourceHom H r,triangularTargetHom H r),triangularCrossHom H r)
  left_inv r := by
    apply bimodule_triangular_ext (ambientBimodule H) <;> rfl
  right_inv r := by
    apply triangular_ext H <;> rfl
  map_add' r s := by
    apply triangular_ext H
    · change bimoduleSourceHom (ambientBimodule H) (r+s) =
        bimoduleSourceHom (ambientBimodule H) r+bimoduleSourceHom (ambientBimodule H) s
      exact map_add _ _ _
    · change bimoduleCrossHom (ambientBimodule H) (r+s) =
        bimoduleCrossHom (ambientBimodule H) r+bimoduleCrossHom (ambientBimodule H) s
      exact map_add _ _ _
    · change bimoduleTargetHom (ambientBimodule H) (r+s) =
        bimoduleTargetHom (ambientBimodule H) r+bimoduleTargetHom (ambientBimodule H) s
      exact map_add _ _ _
  map_mul' r s := by
    apply triangular_ext H
    · rw [(triangularSourceHom H).map_mul]
      change bimoduleSourceHom (ambientBimodule H) (r*s) =
        bimoduleSourceHom (ambientBimodule H) r*bimoduleSourceHom (ambientBimodule H) s
      exact map_mul _ _ _
    · rw [triangularCrossHom_mul]
      change bimoduleCrossHom (ambientBimodule H) (r*s) =
        (bimoduleSourceHom (ambientBimodule H) r : D)*bimoduleCrossHom (ambientBimodule H) s+
        bimoduleCrossHom (ambientBimodule H) r*bimoduleTargetHom (ambientBimodule H) s
      exact bimodule_cross_mul (ambientBimodule H) r s
    · rw [(triangularTargetHom H).map_mul]
      change bimoduleTargetHom (ambientBimodule H) (r*s) =
        bimoduleTargetHom (ambientBimodule H) r*bimoduleTargetHom (ambientBimodule H) s
      exact map_mul _ _ _

theorem ambient_triangular_ring_isomorphism (H : Subfield D) :
    Nonempty (BimoduleTriangularRing (ambientBimodule H) ≃+* TriangularRing H) :=
  ⟨ambientTriangularRingEquiv H⟩

end

end QuantumFlags

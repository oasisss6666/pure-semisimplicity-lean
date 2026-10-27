import QuantumFlags.BimoduleCornerRepresentation

namespace QuantumFlags
noncomputable section
universe u
variable (N : DivisionBimodule.{u})

def bimoduleHomRepresentationModuleMap {M P : HomRepresentation N}
    (f : HomRepresentationMorphism M P) :
    letI := bimoduleModuleFromHomRepresentation N M
    letI := bimoduleModuleFromHomRepresentation N P
    (M.Source × M.Target) →ₗ[(BimoduleTriangularRing N)ᵐᵒᵖ] (P.Source × P.Target) := by
  letI := bimoduleModuleFromHomRepresentation N M
  letI := bimoduleModuleFromHomRepresentation N P
  exact {
    toFun p := (f.source p.1, f.target p.2)
    map_add' p q := by apply Prod.ext <;> simp
    map_smul' r p := by
      apply Prod.ext
      · exact f.source.map_smul ((bimoduleSourceHom N).op r) p.1
      · change f.target (M.arrow p.1 (bimoduleCrossHom N r.unop) +
            (bimoduleTargetHom N).op r • p.2) =
          P.arrow (f.source p.1) (bimoduleCrossHom N r.unop) +
            (bimoduleTargetHom N).op r • f.target p.2
        rw [f.target.map_add, f.target.map_smul]
        rw [LinearMap.congr_fun (f.commutes p.1) (bimoduleCrossHom N r.unop)]
        rfl }

theorem bimoduleHomRepresentationModuleMap_identity (M : HomRepresentation N) :
    letI := bimoduleModuleFromHomRepresentation N M
    bimoduleHomRepresentationModuleMap N (HomRepresentationMorphism.identity M) = LinearMap.id := by
  letI := bimoduleModuleFromHomRepresentation N M
  apply LinearMap.ext
  intro p
  rfl

theorem bimoduleHomRepresentationModuleMap_compose {M P Q : HomRepresentation N}
    (g : HomRepresentationMorphism P Q) (f : HomRepresentationMorphism M P) :
    letI := bimoduleModuleFromHomRepresentation N M
    letI := bimoduleModuleFromHomRepresentation N P
    letI := bimoduleModuleFromHomRepresentation N Q
    bimoduleHomRepresentationModuleMap N (HomRepresentationMorphism.compose g f) =
      (bimoduleHomRepresentationModuleMap N g).comp (bimoduleHomRepresentationModuleMap N f) := by
  letI := bimoduleModuleFromHomRepresentation N M
  letI := bimoduleModuleFromHomRepresentation N P
  letI := bimoduleModuleFromHomRepresentation N Q
  apply LinearMap.ext
  intro p
  rfl

def bimoduleCornerHomRepresentationMap {M P : Type*}
    [AddCommGroup M] [Module (BimoduleTriangularRing N)ᵐᵒᵖ M]
    [AddCommGroup P] [Module (BimoduleTriangularRing N)ᵐᵒᵖ P]
    (g : M →ₗ[(BimoduleTriangularRing N)ᵐᵒᵖ] P) :
    HomRepresentationMorphism (bimoduleCornerHomRepresentation N M)
      (bimoduleCornerHomRepresentation N P) where
  source := cornerFixedMap (bimoduleSourceCornerHom N) g
  target := cornerFixedMap (bimoduleTargetCornerHom N) g
  commutes x := by
    apply LinearMap.ext
    intro n
    apply Subtype.ext
    exact (g.map_smul (MulOpposite.op (bimoduleOffDiagonal N n)) (x : M)).symm

theorem bimoduleCornerHomRepresentationMap_identity (M : Type*)
    [AddCommGroup M] [Module (BimoduleTriangularRing N)ᵐᵒᵖ M] :
    bimoduleCornerHomRepresentationMap N (LinearMap.id : M →ₗ[(BimoduleTriangularRing N)ᵐᵒᵖ] M) =
      HomRepresentationMorphism.identity (bimoduleCornerHomRepresentation N M) := by
  apply HomRepresentationMorphism.ext <;> apply LinearMap.ext <;> intro x <;> rfl

theorem bimoduleCornerHomRepresentationMap_compose {M P Q : Type*}
    [AddCommGroup M] [Module (BimoduleTriangularRing N)ᵐᵒᵖ M]
    [AddCommGroup P] [Module (BimoduleTriangularRing N)ᵐᵒᵖ P]
    [AddCommGroup Q] [Module (BimoduleTriangularRing N)ᵐᵒᵖ Q]
    (g : P →ₗ[(BimoduleTriangularRing N)ᵐᵒᵖ] Q) (f : M →ₗ[(BimoduleTriangularRing N)ᵐᵒᵖ] P) :
    bimoduleCornerHomRepresentationMap N (g.comp f) =
      HomRepresentationMorphism.compose (bimoduleCornerHomRepresentationMap N g)
        (bimoduleCornerHomRepresentationMap N f) := by
  apply HomRepresentationMorphism.ext <;> apply LinearMap.ext <;> intro x <;> rfl

theorem bimoduleCornerModuleEquiv_natural {M P : Type*}
    [AddCommGroup M] [Module (BimoduleTriangularRing N)ᵐᵒᵖ M]
    [AddCommGroup P] [Module (BimoduleTriangularRing N)ᵐᵒᵖ P]
    (g : M →ₗ[(BimoduleTriangularRing N)ᵐᵒᵖ] P) (x : M) :
    bimoduleCornerModuleEquiv N P (g x) =
      bimoduleHomRepresentationModuleMap N (bimoduleCornerHomRepresentationMap N g)
        (bimoduleCornerModuleEquiv N M x) := by
  apply Prod.ext <;> apply Subtype.ext
  · exact (g.map_smul (bimoduleSourceCornerHom N 1) x).symm
  · exact (g.map_smul (bimoduleTargetCornerHom N 1) x).symm

end
end QuantumFlags

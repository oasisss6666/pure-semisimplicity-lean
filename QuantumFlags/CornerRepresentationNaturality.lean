import QuantumFlags.CornerRepresentationRecovery

namespace QuantumFlags

noncomputable section

variable {D : Type*} [DivisionRing D]

theorem cornerHomRepresentation_ambient_arrow (H : Subfield D) (M : Type*) [AddCommGroup M]
    [Module (TriangularRing H)ᵐᵒᵖ M] (x : SourceCorner H M) :
    ambientRepresentationArrow H (cornerHomRepresentation H M) x = cornerArrow H M x := by
  change MulOpposite.op (1 : D) • cornerArrow H M x = cornerArrow H M x
  exact one_smul Dᵐᵒᵖ _

def moduleFromCornerHomEquiv (H : Subfield D) (M : Type*) [AddCommGroup M]
    [Module (TriangularRing H)ᵐᵒᵖ M] :
    letI := moduleFromHomRepresentation H (cornerHomRepresentation H M)
    M ≃ₗ[(TriangularRing H)ᵐᵒᵖ] (SourceCorner H M × TargetCorner H M) := by
  letI := moduleFromHomRepresentation H (cornerHomRepresentation H M)
  exact {
    toAddEquiv := cornerDecomposition H M
    map_smul' r x := by
      have h := (cornerModuleEquiv H M).map_smul r x
      apply Prod.ext <;> apply Subtype.ext
      · have hs := congrArg (fun p : SourceCorner H M × TargetCorner H M => (p.1 : M)) h
        exact hs
      · have ht := congrArg (fun p : SourceCorner H M × TargetCorner H M => (p.2 : M)) h
        change targetCornerHom H 1 • (r • x) =
          targetCornerHom H (MulOpposite.op (triangularCrossHom H r.unop)) •
            (ambientRepresentationArrow H (cornerHomRepresentation H M) (cornerDecomposition H M x).1 : M)+
          targetCornerHom H ((triangularTargetHom H).op r) •
            ((cornerDecomposition H M x).2 : M)
        rw [cornerHomRepresentation_ambient_arrow]
        exact ht }

theorem moduleFromCornerHomEquiv_natural (H : Subfield D) {M : Type*} {P : Type*}
    [AddCommGroup M] [Module (TriangularRing H)ᵐᵒᵖ M]
    [AddCommGroup P] [Module (TriangularRing H)ᵐᵒᵖ P]
    (g : M →ₗ[(TriangularRing H)ᵐᵒᵖ] P) (x : M) :
    moduleFromCornerHomEquiv H P (g x) =
      homRepresentationModuleMap H (cornerHomRepresentationMap H g) (moduleFromCornerHomEquiv H M x) := by
  apply Prod.ext <;> apply Subtype.ext
  · exact (g.map_smul (sourceCornerHom H 1) x).symm
  · exact (g.map_smul (targetCornerHom H 1) x).symm

theorem homRepresentationRecovery_natural (H : Subfield D)
    {M P : HomRepresentation (ambientBimodule H)} (f : HomRepresentationMorphism M P) :
    letI := moduleFromHomRepresentation H M
    letI := moduleFromHomRepresentation H P
    HomRepresentationMorphism.compose (homRepresentationRecovery H P)
      (cornerHomRepresentationMap H (homRepresentationModuleMap H f)) =
      HomRepresentationMorphism.compose f (homRepresentationRecovery H M) := by
  letI : Module Hᵐᵒᵖ M.Source := M.sourceModule
  letI : Module Dᵐᵒᵖ M.Target := M.targetModule
  letI : Module Hᵐᵒᵖ P.Source := P.sourceModule
  letI : Module Dᵐᵒᵖ P.Target := P.targetModule
  letI := moduleFromHomRepresentation H M
  letI := moduleFromHomRepresentation H P
  apply HomRepresentationMorphism.ext <;> apply LinearMap.ext <;> intro x <;> rfl

end

end QuantumFlags

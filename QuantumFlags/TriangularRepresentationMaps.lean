import QuantumFlags.CornerModuleReconstruction

namespace QuantumFlags

noncomputable section

variable {D : Type*} [DivisionRing D]

def triangularMapFromArrows (H : Subfield D)
    {X : Type*} {Y : Type*} {X' : Type*} {Y' : Type*}
    [AddCommGroup X] [Module Hᵐᵒᵖ X] [AddCommGroup Y] [Module Dᵐᵒᵖ Y]
    [AddCommGroup X'] [Module Hᵐᵒᵖ X'] [AddCommGroup Y'] [Module Dᵐᵒᵖ Y']
    (θ : letI := restrictedRightModule H Y; X →ₗ[Hᵐᵒᵖ] Y)
    (θ' : letI := restrictedRightModule H Y'; X' →ₗ[Hᵐᵒᵖ] Y')
    (u : X →ₗ[Hᵐᵒᵖ] X') (v : Y →ₗ[Dᵐᵒᵖ] Y') (hc : ∀ x, θ' (u x) = v (θ x)) :
    letI := triangularModuleFromArrow H X Y θ
    letI := triangularModuleFromArrow H X' Y' θ'
    (X × Y) →ₗ[(TriangularRing H)ᵐᵒᵖ] (X' × Y') := by
  letI := triangularModuleFromArrow H X Y θ
  letI := triangularModuleFromArrow H X' Y' θ'
  exact {
    toFun p := (u p.1,v p.2)
    map_add' p q := by apply Prod.ext <;> simp
    map_smul' r p := by
      apply Prod.ext
      · exact u.map_smul ((triangularSourceHom H).op r) p.1
      · change v (MulOpposite.op (triangularCrossHom H r.unop) • θ p.1+
            (triangularTargetHom H).op r • p.2) =
          MulOpposite.op (triangularCrossHom H r.unop) • θ' (u p.1)+
            (triangularTargetHom H).op r • v p.2
        rw [v.map_add,v.map_smul,v.map_smul,hc] }

theorem triangularMapFromArrows_apply (H : Subfield D)
    {X : Type*} {Y : Type*} {X' : Type*} {Y' : Type*}
    [AddCommGroup X] [Module Hᵐᵒᵖ X] [AddCommGroup Y] [Module Dᵐᵒᵖ Y]
    [AddCommGroup X'] [Module Hᵐᵒᵖ X'] [AddCommGroup Y'] [Module Dᵐᵒᵖ Y']
    (θ : letI := restrictedRightModule H Y; X →ₗ[Hᵐᵒᵖ] Y)
    (θ' : letI := restrictedRightModule H Y'; X' →ₗ[Hᵐᵒᵖ] Y')
    (u : X →ₗ[Hᵐᵒᵖ] X') (v : Y →ₗ[Dᵐᵒᵖ] Y') (hc : ∀ x, θ' (u x) = v (θ x)) (p : X × Y) :
    triangularMapFromArrows H θ θ' u v hc p = (u p.1,v p.2) := rfl

theorem ambientRepresentationArrow_morphism (H : Subfield D)
    {M P : HomRepresentation (ambientBimodule H)} (f : HomRepresentationMorphism M P)
    (x : M.Source) :
    ambientRepresentationArrow H P (f.source x) = f.target (ambientRepresentationArrow H M x) :=
  congrArg (fun φ => φ 1) (f.commutes x)

def homRepresentationModuleMap (H : Subfield D)
    {M P : HomRepresentation (ambientBimodule H)} (f : HomRepresentationMorphism M P) :
    letI := moduleFromHomRepresentation H M
    letI := moduleFromHomRepresentation H P
    (M.Source × M.Target) →ₗ[(TriangularRing H)ᵐᵒᵖ] (P.Source × P.Target) := by
  letI : Module Hᵐᵒᵖ M.Source := M.sourceModule
  letI : Module Dᵐᵒᵖ M.Target := M.targetModule
  letI : Module Hᵐᵒᵖ P.Source := P.sourceModule
  letI : Module Dᵐᵒᵖ P.Target := P.targetModule
  exact triangularMapFromArrows H (ambientRepresentationArrow H M) (ambientRepresentationArrow H P)
    f.source f.target (ambientRepresentationArrow_morphism H f)

theorem homRepresentationModuleMap_identity (H : Subfield D)
    (M : HomRepresentation (ambientBimodule H)) :
    letI := moduleFromHomRepresentation H M
    homRepresentationModuleMap H (HomRepresentationMorphism.identity M) = LinearMap.id := by
  letI := moduleFromHomRepresentation H M
  apply LinearMap.ext
  intro p
  rfl

theorem homRepresentationModuleMap_compose (H : Subfield D)
    {M P Q : HomRepresentation (ambientBimodule H)}
    (g : HomRepresentationMorphism P Q) (f : HomRepresentationMorphism M P) :
    letI := moduleFromHomRepresentation H M
    letI := moduleFromHomRepresentation H P
    letI := moduleFromHomRepresentation H Q
    homRepresentationModuleMap H (HomRepresentationMorphism.compose g f) =
      (homRepresentationModuleMap H g).comp (homRepresentationModuleMap H f) := by
  letI := moduleFromHomRepresentation H M
  letI := moduleFromHomRepresentation H P
  letI := moduleFromHomRepresentation H Q
  apply LinearMap.ext
  intro p
  rfl

abbrev cornerHomRepresentation (H : Subfield D) (M : Type*) [AddCommGroup M]
    [Module (TriangularRing H)ᵐᵒᵖ M] : HomRepresentation (ambientBimodule H) where
  Source := SourceCorner H M
  Target := TargetCorner H M
  arrow := by
    letI := restrictedRightModule H (TargetCorner H M)
    letI := rightHomModule (ambientBimodule H) (TargetCorner H M)
    exact (ambientHomEvaluationEquiv H (TargetCorner H M)).symm.toLinearMap.comp (cornerArrow H M)

theorem cornerHomRepresentation_arrow_apply (H : Subfield D) (M : Type*) [AddCommGroup M]
    [Module (TriangularRing H)ᵐᵒᵖ M] (x : SourceCorner H M) (n : D) :
    (cornerHomRepresentation H M).arrow x n = MulOpposite.op n • cornerArrow H M x := rfl

theorem cornerHomRepresentation_arrow_one (H : Subfield D) (M : Type*) [AddCommGroup M]
    [Module (TriangularRing H)ᵐᵒᵖ M] (x : SourceCorner H M) :
    (cornerHomRepresentation H M).arrow x 1 = cornerArrow H M x := by
  change MulOpposite.op (1 : D) • cornerArrow H M x = cornerArrow H M x
  exact one_smul Dᵐᵒᵖ _

theorem cornerArrow_natural (H : Subfield D) {M : Type*} {P : Type*}
    [AddCommGroup M] [Module (TriangularRing H)ᵐᵒᵖ M]
    [AddCommGroup P] [Module (TriangularRing H)ᵐᵒᵖ P]
    (g : M →ₗ[(TriangularRing H)ᵐᵒᵖ] P) (x : SourceCorner H M) :
    cornerArrow H P (cornerFixedMap (sourceCornerHom H) g x) =
      cornerFixedMap (targetCornerHom H) g (cornerArrow H M x) := by
  apply Subtype.ext
  change MulOpposite.op (offDiagonal H 1) • g (x : M) =
    g (MulOpposite.op (offDiagonal H 1) • (x : M))
  exact (g.map_smul _ _).symm

def cornerHomRepresentationMap (H : Subfield D) {M : Type*} {P : Type*}
    [AddCommGroup M] [Module (TriangularRing H)ᵐᵒᵖ M]
    [AddCommGroup P] [Module (TriangularRing H)ᵐᵒᵖ P]
    (g : M →ₗ[(TriangularRing H)ᵐᵒᵖ] P) :
    HomRepresentationMorphism (cornerHomRepresentation H M) (cornerHomRepresentation H P) where
  source := cornerFixedMap (sourceCornerHom H) g
  target := cornerFixedMap (targetCornerHom H) g
  commutes x := by
    apply LinearMap.ext
    intro n
    change MulOpposite.op n • cornerArrow H P (cornerFixedMap (sourceCornerHom H) g x) =
      cornerFixedMap (targetCornerHom H) g (MulOpposite.op n • cornerArrow H M x)
    rw [cornerArrow_natural,(cornerFixedMap (targetCornerHom H) g).map_smul]

theorem cornerHomRepresentationMap_identity (H : Subfield D) (M : Type*) [AddCommGroup M]
    [Module (TriangularRing H)ᵐᵒᵖ M] :
    cornerHomRepresentationMap H (LinearMap.id : M →ₗ[(TriangularRing H)ᵐᵒᵖ] M) =
      HomRepresentationMorphism.identity (cornerHomRepresentation H M) := by
  apply HomRepresentationMorphism.ext <;> apply LinearMap.ext <;> intro x <;> rfl

theorem cornerHomRepresentationMap_compose (H : Subfield D) {M : Type*} {P : Type*} {Q : Type*}
    [AddCommGroup M] [Module (TriangularRing H)ᵐᵒᵖ M]
    [AddCommGroup P] [Module (TriangularRing H)ᵐᵒᵖ P]
    [AddCommGroup Q] [Module (TriangularRing H)ᵐᵒᵖ Q]
    (g : P →ₗ[(TriangularRing H)ᵐᵒᵖ] Q) (f : M →ₗ[(TriangularRing H)ᵐᵒᵖ] P) :
    cornerHomRepresentationMap H (g.comp f) =
      HomRepresentationMorphism.compose (cornerHomRepresentationMap H g) (cornerHomRepresentationMap H f) := by
  apply HomRepresentationMorphism.ext <;> apply LinearMap.ext <;> intro x <;> rfl

def cornerModuleMap (H : Subfield D) {M : Type*} {P : Type*}
    [AddCommGroup M] [Module (TriangularRing H)ᵐᵒᵖ M]
    [AddCommGroup P] [Module (TriangularRing H)ᵐᵒᵖ P]
    (g : M →ₗ[(TriangularRing H)ᵐᵒᵖ] P) :
    letI := triangularModuleFromArrow H (SourceCorner H M) (TargetCorner H M) (cornerArrow H M)
    letI := triangularModuleFromArrow H (SourceCorner H P) (TargetCorner H P) (cornerArrow H P)
    (SourceCorner H M × TargetCorner H M) →ₗ[(TriangularRing H)ᵐᵒᵖ]
      (SourceCorner H P × TargetCorner H P) :=
  triangularMapFromArrows H (cornerArrow H M) (cornerArrow H P)
    (cornerFixedMap (sourceCornerHom H) g) (cornerFixedMap (targetCornerHom H) g)
    (cornerArrow_natural H g)

theorem cornerModuleEquiv_natural (H : Subfield D) {M : Type*} {P : Type*}
    [AddCommGroup M] [Module (TriangularRing H)ᵐᵒᵖ M]
    [AddCommGroup P] [Module (TriangularRing H)ᵐᵒᵖ P]
    (g : M →ₗ[(TriangularRing H)ᵐᵒᵖ] P) (x : M) :
    cornerModuleEquiv H P (g x) = cornerModuleMap H g (cornerModuleEquiv H M x) := by
  apply Prod.ext <;> apply Subtype.ext
  · exact (g.map_smul (sourceCornerHom H 1) x).symm
  · exact (g.map_smul (targetCornerHom H 1) x).symm

end

end QuantumFlags

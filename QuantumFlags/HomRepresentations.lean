import QuantumFlags.DivisionBimodules

namespace QuantumFlags

noncomputable section

universe u

abbrev BimoduleRightHom (N : DivisionBimodule.{u}) (Y : Type*) [AddCommGroup Y]
    [Module N.RightRingᵐᵒᵖ Y] := N.Space →ₗ[N.RightRingᵐᵒᵖ] Y

@[instance_reducible]
def rightHomModule (N : DivisionBimodule.{u}) (Y : Type*) [AddCommGroup Y]
    [Module N.RightRingᵐᵒᵖ Y] : Module N.LeftRingᵐᵒᵖ (BimoduleRightHom N Y) where
  smul a f := f.comp (bimoduleLeftAction N a.unop)
  one_smul f := by
    apply LinearMap.ext
    intro x
    change f ((1 : N.LeftRing) • x) = f x
    rw [one_smul]
  mul_smul a b f := by
    apply LinearMap.ext
    intro x
    change f ((b.unop*a.unop) • x) = f (b.unop • (a.unop • x))
    rw [mul_smul]
  smul_zero _ := by
    apply LinearMap.ext
    intro x
    rfl
  smul_add _ _ _ := by
    apply LinearMap.ext
    intro x
    rfl
  zero_smul f := by
    apply LinearMap.ext
    intro x
    change f ((0 : N.LeftRing) • x) = 0
    rw [zero_smul,map_zero]
  add_smul a b f := by
    apply LinearMap.ext
    intro x
    change f ((a.unop+b.unop) • x) = f (a.unop • x)+f (b.unop • x)
    rw [add_smul,map_add]

def rightHomMap (N : DivisionBimodule.{u}) {Y : Type*} {Z : Type*} [AddCommGroup Y]
    [Module N.RightRingᵐᵒᵖ Y] [AddCommGroup Z] [Module N.RightRingᵐᵒᵖ Z]
    (f : Y →ₗ[N.RightRingᵐᵒᵖ] Z) :
    letI := rightHomModule N Y
    letI := rightHomModule N Z
    BimoduleRightHom N Y →ₗ[N.LeftRingᵐᵒᵖ] BimoduleRightHom N Z := by
  letI := rightHomModule N Y
  letI := rightHomModule N Z
  exact {
    toFun φ := f.comp φ
    map_add' φ ψ := by
      apply LinearMap.ext
      intro n
      exact f.map_add (φ n) (ψ n)
    map_smul' _ _ := rfl }

theorem rightHomMap_apply (N : DivisionBimodule.{u}) {Y : Type*} {Z : Type*} [AddCommGroup Y]
    [Module N.RightRingᵐᵒᵖ Y] [AddCommGroup Z] [Module N.RightRingᵐᵒᵖ Z]
    (f : Y →ₗ[N.RightRingᵐᵒᵖ] Z) (φ : BimoduleRightHom N Y) (n : N.Space) :
    rightHomMap N f φ n = f (φ n) := rfl

/-- Adjoint Hom data for representations; the tensor description is a separate proof obligation. -/
structure HomRepresentation (N : DivisionBimodule.{u}) where
  Source : Type*
  Target : Type*
  [sourceGroup : AddCommGroup Source]
  [targetGroup : AddCommGroup Target]
  [sourceModule : Module N.LeftRingᵐᵒᵖ Source]
  [targetModule : Module N.RightRingᵐᵒᵖ Target]
  arrow : letI := rightHomModule N Target
    Source →ₗ[N.LeftRingᵐᵒᵖ] BimoduleRightHom N Target

attribute [instance] HomRepresentation.sourceGroup HomRepresentation.targetGroup
  HomRepresentation.sourceModule HomRepresentation.targetModule

structure HomRepresentationMorphism {N : DivisionBimodule.{u}} (M P : HomRepresentation N) where
  source : M.Source →ₗ[N.LeftRingᵐᵒᵖ] P.Source
  target : M.Target →ₗ[N.RightRingᵐᵒᵖ] P.Target
  commutes : ∀ x, P.arrow (source x) = target.comp (M.arrow x)

namespace HomRepresentationMorphism

variable {N : DivisionBimodule.{u}} {M P Q R : HomRepresentation N}

def identity (M : HomRepresentation N) : HomRepresentationMorphism M M where
  source := LinearMap.id
  target := LinearMap.id
  commutes x := rfl

def compose (g : HomRepresentationMorphism P Q) (f : HomRepresentationMorphism M P) :
    HomRepresentationMorphism M Q where
  source := g.source.comp f.source
  target := g.target.comp f.target
  commutes x := by
    change Q.arrow (g.source (f.source x)) = (g.target.comp f.target).comp (M.arrow x)
    rw [g.commutes,f.commutes]
    rfl

theorem ext {f g : HomRepresentationMorphism M P}
    (hs : f.source = g.source) (ht : f.target = g.target) : f = g := by
  cases f
  cases g
  cases hs
  cases ht
  rfl

theorem compose_identity (f : HomRepresentationMorphism M P) : compose f (identity M) = f := by
  apply ext <;> rfl

theorem identity_compose (f : HomRepresentationMorphism M P) : compose (identity P) f = f := by
  apply ext <;> rfl

theorem compose_assoc (h : HomRepresentationMorphism Q R) (g : HomRepresentationMorphism P Q)
    (f : HomRepresentationMorphism M P) : compose (compose h g) f = compose h (compose g f) := by
  apply ext <;> rfl

end HomRepresentationMorphism

end

end QuantumFlags

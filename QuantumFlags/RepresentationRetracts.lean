import QuantumFlags.TensorRepresentationCategory
import QuantumFlags.ReflectionIndecomposable
import QuantumFlags.RetractClosedIndecomposable

namespace QuantumFlags
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v

theorem homArrow_injective_of_retract {N : DivisionBimodule.{u}}
    {M P : HomRepresentation N} (i : HomRepresentationMorphism M P)
    (p : HomRepresentationMorphism P M)
    (h : HomRepresentationMorphism.compose p i = HomRepresentationMorphism.identity M)
    (hP : Function.Injective P.arrow) : Function.Injective M.arrow := by
  intro x y hxy
  have h' : P.arrow (i.source x) = P.arrow (i.source y) := by
    rw [i.commutes, i.commutes, hxy]
  have hsource : p.source.comp i.source = LinearMap.id :=
    congrArg HomRepresentationMorphism.source h
  calc
    x = p.source (i.source x) := (LinearMap.congr_fun hsource x).symm
    _ = p.source (i.source y) := congrArg p.source (hP h')
    _ = y := LinearMap.congr_fun hsource y

theorem tensorArrow_surjective_of_retract {N : DivisionBimodule.{u}}
    {M P : TensorRepresentation N} (i : TensorRepresentationMorphism M P)
    (p : TensorRepresentationMorphism P M)
    (h : TensorRepresentationMorphism.compose p i = TensorRepresentationMorphism.identity M)
    (hP : Function.Surjective P.arrow) : Function.Surjective M.arrow := by
  intro z
  obtain ⟨w, hw⟩ := hP (i.target z)
  refine ⟨balancedTensorMap N P.Source p.source w, ?_⟩
  rw [p.commutes, hw]
  have htarget : p.target.comp i.target = LinearMap.id :=
    congrArg TensorRepresentationMorphism.target h
  exact LinearMap.congr_fun htarget z

variable (N : DivisionBimodule.{u})

def injectiveHomInclusion : InjectiveHomObjects.{u,v} N ⥤
    HomRepresentation.{u, max u v, max u v} N where
  obj M := M.val
  map f := f

instance injectiveHomInclusion_full : (injectiveHomInclusion.{u,v} N).Full where
  map_surjective f := ⟨f, rfl⟩

instance injectiveHomInclusion_faithful : (injectiveHomInclusion.{u,v} N).Faithful where
  map_injective h := h

instance injectiveHomInclusion_additive : (injectiveHomInclusion.{u,v} N).Additive where
  map_add := rfl

theorem injectiveHomInclusion_retract_closed (M : InjectiveHomObjects.{u,v} N)
    (P : HomRepresentation.{u, max u v, max u v} N)
    (i : P ⟶ (injectiveHomInclusion N).obj M)
    (p : (injectiveHomInclusion N).obj M ⟶ P) (h : i ≫ p = 𝟙 P) :
    ∃ P' : InjectiveHomObjects.{u,v} N,
      Nonempty ((injectiveHomInclusion N).obj P' ≅ P) :=
  ⟨⟨P, homArrow_injective_of_retract i p h M.property⟩, ⟨Iso.refl P⟩⟩

theorem injectiveHom_ambient_indecomposable_iff (M : InjectiveHomObjects.{u,v} N) :
    Indecomposable M.val ↔ Indecomposable M :=
  retract_closed_indecomposable_iff (injectiveHomInclusion N)
    (injectiveHomInclusion_retract_closed N) M

variable [FiniteDimensional N.RightRingᵐᵒᵖ N.Space]

def surjectiveDualTensorInclusion : SurjectiveDualTensorObjects.{u,v} N ⥤
    TensorRepresentation.{u, max u v, max u v} (rightDual N) where
  obj M := M.val
  map f := f

instance surjectiveDualTensorInclusion_full : (surjectiveDualTensorInclusion.{u,v} N).Full where
  map_surjective f := ⟨f, rfl⟩

instance surjectiveDualTensorInclusion_faithful :
    (surjectiveDualTensorInclusion.{u,v} N).Faithful where
  map_injective h := h

instance surjectiveDualTensorInclusion_additive :
    (surjectiveDualTensorInclusion.{u,v} N).Additive where
  map_add := rfl

theorem surjectiveDualTensorInclusion_retract_closed (M : SurjectiveDualTensorObjects.{u,v} N)
    (P : TensorRepresentation.{u, max u v, max u v} (rightDual N))
    (i : P ⟶ (surjectiveDualTensorInclusion N).obj M)
    (p : (surjectiveDualTensorInclusion N).obj M ⟶ P) (h : i ≫ p = 𝟙 P) :
    ∃ P' : SurjectiveDualTensorObjects.{u,v} N,
      Nonempty ((surjectiveDualTensorInclusion N).obj P' ≅ P) :=
  ⟨⟨P, tensorArrow_surjective_of_retract i p h M.property⟩, ⟨Iso.refl P⟩⟩

theorem surjectiveDualTensor_ambient_indecomposable_iff (M : SurjectiveDualTensorObjects.{u,v} N) :
    Indecomposable M.val ↔ Indecomposable M :=
  retract_closed_indecomposable_iff (surjectiveDualTensorInclusion N)
    (surjectiveDualTensorInclusion_retract_closed N) M

theorem reflection_ambient_indecomposable_iff (M : InjectiveHomObjects.{u,v} N) :
    Indecomposable (reflectionForward N M.val) ↔ Indecomposable M.val :=
  (surjectiveDualTensor_ambient_indecomposable_iff N ((reflectionFunctor N).obj M)).trans
    ((reflection_indecomposable_iff N M).trans
      (injectiveHom_ambient_indecomposable_iff N M).symm)

theorem inverseReflection_ambient_indecomposable_iff (L : SurjectiveDualTensorObjects.{u,v} N) :
    Indecomposable (reflectionBackward N L.val) ↔ Indecomposable L.val :=
  (injectiveHom_ambient_indecomposable_iff N ((inverseReflectionFunctor N).obj L)).trans
    ((inverseReflection_indecomposable_iff N L).trans
      (surjectiveDualTensor_ambient_indecomposable_iff N L).symm)

end
end QuantumFlags

import QuantumFlags.TensorReflectionEquivalence

namespace QuantumFlags
noncomputable section
open CategoryTheory
universe u v
variable (N : DivisionBimodule.{u}) [FiniteDimensional N.RightRingᵐᵒᵖ N.Space]

def tensorReflectionRecoverIso
    (M : InjectiveTensorObjects.{u,v} N)
    (L : SurjectiveDualTensorObjects.{u,v} N)
    (e : reflectionForward N (tensorRepresentationToHom M.val) ≅ L.val) :
    M.val ≅ homRepresentationToTensor (reflectionBackward N L.val) := by
  let E := tensorReflectionEquivalence N
  let e' : E.functor.obj M ≅ L := {
    hom := e.hom
    inv := e.inv
    hom_inv_id := e.hom_inv_id
    inv_hom_id := e.inv_hom_id }
  let d := E.unitIso.app M ≪≫ E.inverse.mapIso e'
  exact {
    hom := d.hom
    inv := d.inv
    hom_inv_id := d.hom_inv_id
    inv_hom_id := d.inv_hom_id }

theorem tensorReflectionRecoverIso_exists
    (M : InjectiveTensorObjects.{u,v} N)
    (L : SurjectiveDualTensorObjects.{u,v} N)
    (e : reflectionForward N (tensorRepresentationToHom M.val) ≅ L.val) :
    Nonempty (M.val ≅ homRepresentationToTensor (reflectionBackward N L.val)) :=
  ⟨tensorReflectionRecoverIso N M L e⟩

end
end QuantumFlags

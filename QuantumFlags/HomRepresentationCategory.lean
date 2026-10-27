import QuantumFlags.HomRepresentationProducts
import Mathlib.CategoryTheory.Preadditive.Biproducts

namespace QuantumFlags
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
variable (N : DivisionBimodule.{u})

instance homRepresentationCategory : Category (HomRepresentation.{u, max u v, max u v} N) where
  Hom M P := HomRepresentationMorphism M P
  id M := HomRepresentationMorphism.identity M
  comp f g := HomRepresentationMorphism.compose g f
  id_comp f := HomRepresentationMorphism.compose_identity f
  comp_id f := HomRepresentationMorphism.identity_compose f
  assoc f g h := (HomRepresentationMorphism.compose_assoc h g f).symm

instance homRepresentationPreadditive : Preadditive (HomRepresentation.{u, max u v, max u v} N) where
  homGroup M P := HomRepresentationMorphism.addCommGroup M P
  add_comp M P Q f g h := by
    apply HomRepresentationMorphism.ext
    · apply LinearMap.ext
      intro x
      exact h.source.map_add _ _
    · apply LinearMap.ext
      intro y
      exact h.target.map_add _ _
  comp_add M P Q f g h := by
    apply HomRepresentationMorphism.ext <;> rfl

def homRepresentationBicone (M P : HomRepresentation.{u, max u v, max u v} N) :
    BinaryBicone M P where
  pt := homRepresentationProd M P
  fst := homProdFst M P
  snd := homProdSnd M P
  inl := homProdInl M P
  inr := homProdInr M P
  inl_fst := homProd_inl_fst M P
  inl_snd := homProd_inl_snd M P
  inr_fst := homProd_inr_fst M P
  inr_snd := homProd_inr_snd M P

theorem homRepresentationBicone_total (M P : HomRepresentation.{u, max u v, max u v} N) :
    (homRepresentationBicone N M P).fst ≫ (homRepresentationBicone N M P).inl +
      (homRepresentationBicone N M P).snd ≫ (homRepresentationBicone N M P).inr =
        𝟙 (homRepresentationBicone N M P).pt :=
  homProd_total M P

instance homRepresentationHasBinaryBiproducts :
    HasBinaryBiproducts (HomRepresentation.{u, max u v, max u v} N) where
  has_binary_biproduct M P := hasBinaryBiproduct_of_total
    (homRepresentationBicone N M P) (homRepresentationBicone_total N M P)

end
end QuantumFlags

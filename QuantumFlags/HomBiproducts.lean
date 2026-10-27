import QuantumFlags.HomRepresentationProducts
import QuantumFlags.ReflectionPreadditive
import Mathlib.CategoryTheory.Preadditive.Biproducts

namespace QuantumFlags
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
variable (N : DivisionBimodule.{u})

def injectiveHomBicone (M P : InjectiveHomObjects.{u,v} N) : BinaryBicone M P where
  pt := ⟨homRepresentationProd M.val P.val, homRepresentationProd_injective M.property P.property⟩
  fst := homProdFst M.val P.val
  snd := homProdSnd M.val P.val
  inl := homProdInl M.val P.val
  inr := homProdInr M.val P.val
  inl_fst := homProd_inl_fst M.val P.val
  inl_snd := homProd_inl_snd M.val P.val
  inr_fst := homProd_inr_fst M.val P.val
  inr_snd := homProd_inr_snd M.val P.val

theorem injectiveHomBicone_total (M P : InjectiveHomObjects.{u,v} N) :
    (injectiveHomBicone N M P).fst ≫ (injectiveHomBicone N M P).inl +
      (injectiveHomBicone N M P).snd ≫ (injectiveHomBicone N M P).inr =
        𝟙 (injectiveHomBicone N M P).pt :=
  homProd_total M.val P.val

instance injectiveHomHasBinaryBiproducts : HasBinaryBiproducts (InjectiveHomObjects.{u,v} N) where
  has_binary_biproduct M P := hasBinaryBiproduct_of_total
    (injectiveHomBicone N M P) (injectiveHomBicone_total N M P)

end
end QuantumFlags

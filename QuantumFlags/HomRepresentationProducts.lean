import QuantumFlags.RepresentationMorphismAddition

namespace QuantumFlags
noncomputable section
universe u
variable {N : DivisionBimodule.{u}}

abbrev homRepresentationProd (M P : HomRepresentation N) : HomRepresentation N where
  Source := M.Source × P.Source
  Target := M.Target × P.Target
  arrow := by
    letI := rightHomModule N M.Target
    letI := rightHomModule N P.Target
    letI := rightHomModule N (M.Target × P.Target)
    exact {
      toFun x := {
        toFun n := (M.arrow x.1 n,P.arrow x.2 n)
        map_add' n m := Prod.ext ((M.arrow x.1).map_add n m) ((P.arrow x.2).map_add n m)
        map_smul' b n := Prod.ext ((M.arrow x.1).map_smul b n) ((P.arrow x.2).map_smul b n) }
      map_add' x y := by
        apply LinearMap.ext
        intro n
        apply Prod.ext
        · exact LinearMap.congr_fun (M.arrow.map_add x.1 y.1) n
        · exact LinearMap.congr_fun (P.arrow.map_add x.2 y.2) n
      map_smul' a x := by
        apply LinearMap.ext
        intro n
        apply Prod.ext
        · have h := LinearMap.congr_fun (M.arrow.map_smul a x.1) n
          exact h
        · have h := LinearMap.congr_fun (P.arrow.map_smul a x.2) n
          exact h }

def homProdInl (M P : HomRepresentation N) : HomRepresentationMorphism M (homRepresentationProd M P) where
  source := LinearMap.inl _ _ _
  target := LinearMap.inl _ _ _
  commutes x := by
    apply LinearMap.ext
    intro n
    change (M.arrow x n,P.arrow 0 n) = (M.arrow x n,0)
    rw [map_zero]
    rfl

def homProdInr (M P : HomRepresentation N) : HomRepresentationMorphism P (homRepresentationProd M P) where
  source := LinearMap.inr _ _ _
  target := LinearMap.inr _ _ _
  commutes x := by
    apply LinearMap.ext
    intro n
    change (M.arrow 0 n,P.arrow x n) = (0,P.arrow x n)
    rw [map_zero]
    rfl

def homProdFst (M P : HomRepresentation N) : HomRepresentationMorphism (homRepresentationProd M P) M where
  source := LinearMap.fst _ _ _
  target := LinearMap.fst _ _ _
  commutes x := by apply LinearMap.ext; intro n; rfl

def homProdSnd (M P : HomRepresentation N) : HomRepresentationMorphism (homRepresentationProd M P) P where
  source := LinearMap.snd _ _ _
  target := LinearMap.snd _ _ _
  commutes x := by apply LinearMap.ext; intro n; rfl

theorem homRepresentationProd_injective {M P : HomRepresentation N}
    (hM : Function.Injective M.arrow) (hP : Function.Injective P.arrow) :
    Function.Injective (homRepresentationProd M P).arrow := by
  intro x y h
  apply Prod.ext
  · apply hM
    apply LinearMap.ext
    intro n
    exact congrArg Prod.fst (LinearMap.congr_fun h n)
  · apply hP
    apply LinearMap.ext
    intro n
    exact congrArg Prod.snd (LinearMap.congr_fun h n)

theorem homProd_inl_fst (M P : HomRepresentation N) :
    HomRepresentationMorphism.compose (homProdFst M P) (homProdInl M P) =
      HomRepresentationMorphism.identity M := by
  apply HomRepresentationMorphism.ext <;> rfl

theorem homProd_inr_snd (M P : HomRepresentation N) :
    HomRepresentationMorphism.compose (homProdSnd M P) (homProdInr M P) =
      HomRepresentationMorphism.identity P := by
  apply HomRepresentationMorphism.ext <;> rfl

theorem homProd_inl_snd (M P : HomRepresentation N) :
    HomRepresentationMorphism.compose (homProdSnd M P) (homProdInl M P) = 0 := by
  apply HomRepresentationMorphism.ext <;> rfl

theorem homProd_inr_fst (M P : HomRepresentation N) :
    HomRepresentationMorphism.compose (homProdFst M P) (homProdInr M P) = 0 := by
  apply HomRepresentationMorphism.ext <;> rfl

theorem homProd_total (M P : HomRepresentation N) :
    HomRepresentationMorphism.compose (homProdInl M P) (homProdFst M P)+
      HomRepresentationMorphism.compose (homProdInr M P) (homProdSnd M P) =
        HomRepresentationMorphism.identity (homRepresentationProd M P) := by
  apply HomRepresentationMorphism.ext
  · apply LinearMap.ext
    intro x
    change (x.1,0)+(0,x.2) = x
    simp
  · apply LinearMap.ext
    intro y
    change (y.1,0)+(0,y.2) = y
    simp

end
end QuantumFlags

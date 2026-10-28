import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresentationMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringPresentationResolution

/-! # Family Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.FamilyRefinement.Family

noncomputable section

/-! A genuine refinement of a frame family gives an augmented map of
the original free presentation resolutions. -/

open _root_.CategoryTheory Opposite

universe u v

variable {C : Type (max u v)} [Category.{v} C] {ι κ : Type v}
  (F : ι → C) (G : κ → C) (ρ : ι → κ) (α : ∀ i, F i ⟶ G (ρ i))

def presentationMap : CoveringPresentationPresheaf.presentations F ⟶
    CoveringPresentationPresheaf.presentations G where
  app _ := ↾fun x => ⟨⟨ρ x.down.1, x.down.2 ≫ α x.down.1⟩⟩
  naturality _ _ f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply ULift.ext
    refine Sigma.ext rfl ?_
    exact heq_of_eq (Category.assoc f.unop x.down.2 (α x.down.1))

variable (R : Type (max u v)) [CommRing R] (J : GrothendieckTopology C)

def map : CoveringPresentationResolution.complex J R F ⟶
    CoveringPresentationResolution.complex J R G :=
  ((presheafToSheaf J (ModuleCat.{max u v} R)).mapHomologicalComplex (.down ℕ)).map
    (Cech.PresentationMap.map R (presentationMap F G ρ α))

theorem augmentation : Family.map F G ρ α R J ≫ CoveringPresentationResolution.augmentation J R G =
    CoveringPresentationResolution.augmentation J R F := by
  let S := (presheafToSheaf J (ModuleCat.{max u v} R)).mapHomologicalComplex (.down ℕ)
  let a := Cech.PresentationMap.map R (presentationMap F G ρ α)
  let ε := AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.augmentation R (CoveringPresentationPresheaf.presentations G)
  let η := AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.augmentation R (CoveringPresentationPresheaf.presentations F)
  let e := (HomologicalComplex.singleMapHomologicalComplex (presheafToSheaf J (ModuleCat.{max u v} R))
    (.down ℕ) 0).hom.app (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.coefficientPresheaf (C := C) R)
  change S.map a ≫ (S.map ε ≫ e) = S.map η ≫ e
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun b => b ≫ e) ((S.map_comp a ε).symm.trans
      (congrArg S.map (Cech.PresentationMap.augmentation R (presentationMap F G ρ α)))))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.FamilyRefinement.Family

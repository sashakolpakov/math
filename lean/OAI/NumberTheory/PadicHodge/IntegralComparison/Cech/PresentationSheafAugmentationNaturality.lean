import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresentationSheafAugmentation

/-! # Presentation Sheaf Augmentation Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresentationSheafAugmentationNaturality

noncomputable section

/-! Restriction of original presentation resolutions respects their constant-coefficient augmentations. -/

open _root_.CategoryTheory

open OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresentationSheafRestriction

universe u v w v' w'

variable (R : Type u) [CommRing R] {C : Type v} [Category.{w} C]
  {D : Type v'} [Category.{w'} D] (G : C ⥤ D)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasSheafify J (ModuleCat.{u} R)] [HasSheafify K (ModuleCat.{u} R)]
  [G.IsContinuous J K] [G.IsCocontinuous J K]
  [∀ (F : Cᵒᵖ ⥤ ModuleCat.{u} R), G.op.HasPointwiseRightKanExtension F]
  {F : Cᵒᵖ ⥤ Type u} {H : Dᵒᵖ ⥤ Type u} (a : F ⟶ G.op ⋙ H)

theorem presheaf_zero : (PresentationSheafRestriction.map R G J K a).f 0 ≫ (PresentationSheafRestriction.restriction R G J K).map
    ((presheafToSheaf K (ModuleCat.{u} R)).map ((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.augmentation R H).f 0)) =
      (presheafToSheaf J (ModuleCat.{u} R)).map ((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.augmentation R F).f 0) ≫
        (PresentationSheafRestriction.constantIso R G J K).inv := by
  let S := presheafToSheaf J (ModuleCat.{u} R)
  let b := (PresentationRestriction.map R G a).f 0
  let ε := (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.augmentation R H).f 0
  let η := (PresentationSheafRestriction.compatibility R G J K).hom
  have hn := η.naturality ε
  have ha := (S.map_comp b ((PresentationRestriction.restriction R G).map ε)).symm.trans
    (congrArg S.map (PresentationRestriction.map_augmentation_zero R G a))
  change (S.map b ≫ η.app ((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.complex R H).X 0)) ≫ _ =
    S.map ((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.augmentation R F).f 0) ≫
      η.app (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.coefficientPresheaf (C := D) R)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun c => S.map b ≫ c) hn.symm).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun c => c ≫ η.app (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.coefficientPresheaf (C := D) R)) ha)))

theorem zero : (PresentationSheafRestriction.map R G J K a).f 0 ≫ (PresentationSheafRestriction.restriction R G J K).map
    ((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.sheafAugmentation R H K).f 0) =
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.sheafAugmentation R F J).f 0 ≫ (PresentationSheafRestriction.constantIso R G J K).inv := by
  exact (congrArg (fun b => (PresentationSheafRestriction.map R G J K a).f 0 ≫ (PresentationSheafRestriction.restriction R G J K).map b)
    (PresentationSheafAugmentation.zero R H K)).trans
      ((presheaf_zero R G J K a).trans
        (congrArg (fun b => b ≫ (PresentationSheafRestriction.constantIso R G J K).inv) (PresentationSheafAugmentation.zero R F J).symm))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresentationSheafAugmentationNaturality

import OAI.AlgebraicGeometry.Comparison.Betti.Analytic.AugmentationInt
import OAI.AlgebraicGeometry.Comparison.Betti.Derived.ResolutionNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.Derived.ConstantPullback

/-! # Resolution Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Analytic.ResolutionNaturality

noncomputable section

/-! The proved analytic resolution and its inverse commute with actual scheme pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y)

abbrev schemeAnalyticInverseImage : Betti.Smooth.SheafMap.AnalyticComplexSheaves Y ⥤ Betti.Smooth.SheafMap.AnalyticComplexSheaves X :=
  TopologicalSheafPullback.sheafInverseImage (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)

instance schemeAnalyticInverseImageAdditive : (schemeAnalyticInverseImage f).Additive :=
  TopologicalSheafPullback.sheafInverseImageAdditive (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)

instance schemeAnalyticInverseImageLimits : PreservesFiniteLimits (schemeAnalyticInverseImage f) :=
  TopologicalSheafPullback.sheafInverseImageLimits (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)

instance schemeAnalyticInverseImageColimits : PreservesFiniteColimits (schemeAnalyticInverseImage f) :=
  TopologicalSheafPullback.sheafInverseImageColimits (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)

instance schemeAnalyticInverseImageLinear : (schemeAnalyticInverseImage f).Linear ℂ :=
  Derived.ConstantPullback.sheafInverseImageLinear (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)

def schemeAnalyticDerivedConstantIso :
    (schemeAnalyticInverseImage f).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (Betti.Smooth.SheafMap.AnalyticComplexSheaves Y) 0).obj (De.analyticConstantSheaf Y)) ≅
      (DerivedCategory.singleFunctor (Betti.Smooth.SheafMap.AnalyticComplexSheaves X) 0).obj (De.analyticConstantSheaf X) :=
  ((schemeAnalyticInverseImage f).mapDerivedCategorySingleFunctor 0).app (De.analyticConstantSheaf Y) ≪≫
    (DerivedCategory.singleFunctor (Betti.Smooth.SheafMap.AnalyticComplexSheaves X) 0).mapIso
      (TopologicalSheafPullback.constantPullbackIso (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f))

variable [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]

def derivedAnalyticDeRhamPullback :
    (schemeAnalyticInverseImage f).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (De.analyticDeRhamSheafComplexInt Y)) ⟶
      DerivedCategory.Q.obj (De.analyticDeRhamSheafComplexInt X) :=
  Derived.ResolutionNaturality.Ext.derivedComplexMap (schemeAnalyticInverseImage f) (InverseNaturalityInt.schemeAnalyticDeRhamPullbackInt f)

theorem analyticDeRhamResolutionIso_naturality :
    (schemeAnalyticInverseImage f).mapDerivedCategory.map (De.analyticDeRhamResolutionIso Y).hom ≫
        derivedAnalyticDeRhamPullback f =
      (schemeAnalyticDerivedConstantIso f).hom ≫ (De.analyticDeRhamResolutionIso X).hom := by
  have h := Derived.ResolutionNaturality.Ext.derived_augmentation_square.{1, 1} (schemeAnalyticInverseImage f)
    (De.analyticDeRhamAugmentationInt Y) (De.analyticDeRhamAugmentationInt X)
    (InverseNaturalityInt.schemeAnalyticDeRhamPullbackInt f)
    (TopologicalSheafPullback.constantPullbackIso (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)).hom
    (AugmentationInt.analyticDeRhamAugmentationInt_naturality f)
  exact h.trans (Category.assoc
    (((schemeAnalyticInverseImage f).mapDerivedCategorySingleFunctor 0).hom.app (De.analyticConstantSheaf Y))
    ((DerivedCategory.singleFunctor (Betti.Smooth.SheafMap.AnalyticComplexSheaves X) 0).map
      (TopologicalSheafPullback.constantPullbackIso (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)).hom)
    (DerivedCategory.Q.map (De.analyticDeRhamAugmentationInt X))).symm

theorem analyticDeRhamResolutionIso_inv_naturality :
    derivedAnalyticDeRhamPullback f ≫ (De.analyticDeRhamResolutionIso X).inv =
      (schemeAnalyticInverseImage f).mapDerivedCategory.map (De.analyticDeRhamResolutionIso Y).inv ≫
        (schemeAnalyticDerivedConstantIso f).hom := by
  let a := (schemeAnalyticInverseImage f).mapDerivedCategory.mapIso (De.analyticDeRhamResolutionIso Y)
  let b := De.analyticDeRhamResolutionIso X
  let c := schemeAnalyticDerivedConstantIso f
  let p := derivedAnalyticDeRhamPullback f
  have h : a.hom ≫ p = c.hom ≫ b.hom := analyticDeRhamResolutionIso_naturality f
  change p ≫ b.inv = a.inv ≫ c.hom
  apply (Iso.cancel_iso_hom_left a _ _).mp
  rw [← Category.assoc a.hom p, h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

end

end OAI.AlgebraicGeometry.Comparison.Betti.Analytic.ResolutionNaturality

import OAI.AlgebraicGeometry.Comparison.Betti.Analytic.PullbackExtension
import OAI.AlgebraicGeometry.Comparison.Betti.AugmentationExtension
import OAI.AlgebraicGeometry.Comparison.Betti.Analytic.De

/-! # Augmentation Int -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Analytic.AugmentationInt

noncomputable section

/-! Naturality of the actual constant augmentation on the integer analytic complex. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

attribute [local instance] RealizationNaturality.nativePointSpaceCharted RealizationNaturality.nativePointSpaceManifold

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] (f : X ⟶ Y)

theorem analyticDeRhamAugmentationInt_naturality :
    Derived.ResolutionFunctor.Ext.mappedAugmentation (TopologicalSheafPullback.sheafInverseImage (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f))
        (De.analyticDeRhamAugmentationInt Y) ≫ InverseNaturalityInt.schemeAnalyticDeRhamPullbackInt f =
      (CochainComplex.singleFunctor (Betti.Smooth.SheafMap.AnalyticComplexSheaves X) 0).map
        (TopologicalSheafPullback.constantPullbackIso (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)).hom ≫
          De.analyticDeRhamAugmentationInt X := by
  let F : Betti.Smooth.SheafMap.AnalyticComplexSheaves Y ⥤ Betti.Smooth.SheafMap.AnalyticComplexSheaves X :=
    TopologicalSheafPullback.sheafInverseImage (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
  let : F.Additive := TopologicalSheafPullback.sheafInverseImageAdditive (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
  let a : (CochainComplex.single₀ (Betti.Smooth.SheafMap.AnalyticComplexSheaves Y)).obj (De.analyticConstantSheaf Y) ⟶
      NaturalityInt.schemeAnalyticFormsNat Y := Analysis.DifferentialForms.Manifold.DeRhamResolution.manifoldDeRhamSheafAugmentation (RegularSmoothness.NativeModel Y) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)
  let b : (CochainComplex.single₀ (Betti.Smooth.SheafMap.AnalyticComplexSheaves X)).obj (De.analyticConstantSheaf X) ⟶
      NaturalityInt.schemeAnalyticFormsNat X := Analysis.DifferentialForms.Manifold.DeRhamResolution.manifoldDeRhamSheafAugmentation (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
  let φ : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (NaturalityInt.schemeAnalyticFormsNat Y) ⟶
      NaturalityInt.schemeAnalyticFormsNat X := PullbackExtension.schemeAnalyticDeRhamPullbackNat f
  let u : F.obj (De.analyticConstantSheaf Y) ⟶ De.analyticConstantSheaf X :=
    (TopologicalSheafPullback.constantPullbackIso (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)).hom
  have h : F.map (AugmentationExtension.Complex.augmentationZero a) ≫ φ.f 0 =
      u ≫ AugmentationExtension.Complex.augmentationZero b := by
    exact @AugmentationNaturality.Smooth.analyticDeRhamPullback_constant (RegularSmoothness.NativeModel X) (RegularSmoothness.NativeModel Y) _ _ _ _
      (Betti.Scheme.schemePointSpace X) (Betti.Scheme.schemePointSpace Y)
      (RealizationNaturality.nativePointSpaceCharted X) (RealizationNaturality.nativePointSpaceCharted Y)
      (RealizationNaturality.nativePointSpaceManifold X) (RealizationNaturality.nativePointSpaceManifold Y)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map f ∞)
  erw [PullbackExtension.schemeAnalyticDeRhamPullbackInt_extension f]
  exact AugmentationExtension.Complex.extendAugmentation_square F a b φ u h

end

end OAI.AlgebraicGeometry.Comparison.Betti.Analytic.AugmentationInt

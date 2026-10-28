import OAI.AlgebraicGeometry.Comparison.Betti.Analytic.InverseNaturalityInt
import OAI.AlgebraicGeometry.Comparison.Betti.Analytic.AugmentationNaturality

/-! # Pullback Extension -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Analytic.PullbackExtension

noncomputable section

/-! The actual analytic pullback on integer complexes extends the smooth pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

attribute [local instance] RealizationNaturality.nativePointSpaceCharted RealizationNaturality.nativePointSpaceManifold

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] (f : X ⟶ Y)

def schemeAnalyticDeRhamPullbackNat :
    ((TopologicalSheafPullback.sheafInverseImage (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (NaturalityInt.schemeAnalyticFormsNat Y) ⟶ NaturalityInt.schemeAnalyticFormsNat X :=
  SheafPullback.Smooth.analyticDeRhamPullback (E := RegularSmoothness.NativeModel X) (F := RegularSmoothness.NativeModel Y)
    (M := Betti.Scheme.schemePointSpace X) (N := Betti.Scheme.schemePointSpace Y) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
    (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map f ∞)

theorem schemeAnalyticDeRhamPullbackNat_normalization :
    (SingularGlobalNaturality.sheafImageCochainAdjunction (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)).homEquiv _ _
      (schemeAnalyticDeRhamPullbackNat f) = NaturalityInt.schemeAnalyticDeRhamDirectImage f :=
  (SingularGlobalNaturality.sheafImageCochainAdjunction (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)).homEquiv _ _
    |>.apply_symm_apply _

theorem schemeAnalyticDeRhamPullbackInt_extension :
    InverseNaturalityInt.schemeAnalyticDeRhamPullbackInt f =
      (Complex.Extension.mapExtendIso (TopologicalSheafPullback.sheafInverseImage (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f))
        (ComplexShape.embeddingUpIntGE 0) (NaturalityInt.schemeAnalyticFormsNat Y)).hom ≫
      HomologicalComplex.extendMap (schemeAnalyticDeRhamPullbackNat f) (ComplexShape.embeddingUpIntGE 0) := by
  let F : Betti.Smooth.SheafMap.AnalyticComplexSheaves Y ⥤ Betti.Smooth.SheafMap.AnalyticComplexSheaves X :=
    TopologicalSheafPullback.sheafInverseImage (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
  let G : Betti.Smooth.SheafMap.AnalyticComplexSheaves X ⥤ Betti.Smooth.SheafMap.AnalyticComplexSheaves Y :=
    TopologicalSheafPullback.sheafDirectImage (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
  let : F.Additive := TopologicalSheafPullback.sheafInverseImageAdditive (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
  let : G.Additive := TopologicalSheafPullback.sheafDirectImageAdditive (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
  let adj : F ⊣ G := TopologicalSheafPullback.sheafImageAdjunction (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
  let pn : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (NaturalityInt.schemeAnalyticFormsNat Y) ⟶
      NaturalityInt.schemeAnalyticFormsNat X := schemeAnalyticDeRhamPullbackNat f
  have hn : (Complex.Adjunction.onComplexes adj (ComplexShape.up ℕ)).homEquiv _ _ pn =
      NaturalityInt.schemeAnalyticDeRhamDirectImage f := schemeAnalyticDeRhamPullbackNat_normalization f
  have h := AdjunctionExtension.homEquiv_extend adj (ComplexShape.embeddingUpIntGE 0) pn
  erw [hn] at h
  apply ((InverseNaturalityInt.schemeAnalyticImageAdjunctionInt f).homEquiv _ _).injective
  erw [InverseNaturalityInt.schemeAnalyticDeRhamPullbackInt_normalization]
  exact h.symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.Analytic.PullbackExtension

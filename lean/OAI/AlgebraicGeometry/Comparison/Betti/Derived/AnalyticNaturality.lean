import OAI.AlgebraicGeometry.Comparison.Betti.Analytification.MateNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.Derived.ComplexSquare

/-! # Analytic Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Derived.AnalyticNaturality

noncomputable section

/-! Naturality of the original algebraic-to-analytic realization in the derived category. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] (f : X ⟶ Y)

theorem algebraicToAnalyticSheafMapInt_mate_naturality :
    ((Analytic.ResolutionNaturality.schemeAnalyticInverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (Analytic.De.algebraicToAnalyticSheafMapInt Y) ≫ Analytic.InverseNaturalityInt.schemeAnalyticDeRhamPullbackInt f =
    (NatTrans.mapHomologicalComplex (Analytification.MateNaturality.analytificationSheafMateIso f).inv (ComplexShape.up ℤ)).app
        (Algebraic.Sheaves.algebraicDeRhamSheafComplexInt Y) ≫
      ((Analytic.De.analytificationInverseImage X).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (OpenForms.deRhamSheafPullbackInt f) ≫ Analytic.De.algebraicToAnalyticSheafMapInt X := by
  erw [Analytification.MateNaturality.analytificationSheafMateIso_inv_onComplexes]
  exact Analytic.InverseNaturalityInt.algebraicToAnalyticSheafMapInt_naturality f

theorem derivedAlgebraicToAnalyticForms_naturality :
    (Analytic.ResolutionNaturality.schemeAnalyticInverseImage f).mapDerivedCategory.map (Analytic.De.derivedAlgebraicToAnalyticForms Y) ≫
        Analytic.ResolutionNaturality.derivedAnalyticDeRhamPullback f =
      (Analytification.MateNaturality.derivedAnalytificationMateIso f).inv.app (DerivedCategory.Q.obj (Algebraic.Sheaves.algebraicDeRhamSheafComplexInt Y)) ≫
        (Analytic.De.derivedAnalytificationInverseImage X).map (OpenForms.derivedDeRhamPullback f) ≫
          Analytic.De.derivedAlgebraicToAnalyticForms X :=
  ComplexSquare.derivedComplexMap_square.{1, 1, 1, 1}
    (Algebraic.Sheaves.inverseImage f) (Analytic.De.analytificationInverseImage X) (Analytic.De.analytificationInverseImage Y)
    (Analytic.ResolutionNaturality.schemeAnalyticInverseImage f) (Analytification.MateNaturality.analytificationSheafMateIso f)
    (OpenForms.deRhamSheafPullbackInt f) (Analytic.De.algebraicToAnalyticSheafMapInt X)
    (Analytic.De.algebraicToAnalyticSheafMapInt Y) (Analytic.InverseNaturalityInt.schemeAnalyticDeRhamPullbackInt f)
    (algebraicToAnalyticSheafMapInt_mate_naturality f)

theorem derivedAlgebraicToAnalyticConstant_naturality :
    (Analytic.ResolutionNaturality.schemeAnalyticInverseImage f).mapDerivedCategory.map (Analytic.De.derivedAlgebraicToAnalyticConstant Y) ≫
        (Analytic.ResolutionNaturality.schemeAnalyticDerivedConstantIso f).hom =
      (Analytification.MateNaturality.derivedAnalytificationMateIso f).inv.app (DerivedCategory.Q.obj (Algebraic.Sheaves.algebraicDeRhamSheafComplexInt Y)) ≫
        (Analytic.De.derivedAnalytificationInverseImage X).map (OpenForms.derivedDeRhamPullback f) ≫
          Analytic.De.derivedAlgebraicToAnalyticConstant X := by
  let J := (Analytic.ResolutionNaturality.schemeAnalyticInverseImage f).mapDerivedCategory
  let rY := Analytic.De.derivedAlgebraicToAnalyticForms Y
  let rX := Analytic.De.derivedAlgebraicToAnalyticForms X
  let bY := Analytic.De.analyticDeRhamResolutionIso Y
  let bX := Analytic.De.analyticDeRhamResolutionIso X
  let c := Analytic.ResolutionNaturality.schemeAnalyticDerivedConstantIso f
  let p := Analytic.ResolutionNaturality.derivedAnalyticDeRhamPullback f
  let e := (Analytification.MateNaturality.derivedAnalytificationMateIso f).inv.app
    (DerivedCategory.Q.obj (Algebraic.Sheaves.algebraicDeRhamSheafComplexInt Y))
  let q := (Analytic.De.derivedAnalytificationInverseImage X).map (OpenForms.derivedDeRhamPullback f)
  have h : J.map rY ≫ p = e ≫ q ≫ rX := derivedAlgebraicToAnalyticForms_naturality f
  have hi : p ≫ bX.inv = J.map bY.inv ≫ c.hom := Analytic.ResolutionNaturality.analyticDeRhamResolutionIso_inv_naturality f
  change J.map (rY ≫ bY.inv) ≫ c.hom = e ≫ q ≫ rX ≫ bX.inv
  erw [J.map_comp rY bY.inv, Category.assoc, ← hi, ← Category.assoc (J.map rY) p, h]
  simp only [Category.assoc]

end

end OAI.AlgebraicGeometry.Comparison.Betti.Derived.AnalyticNaturality

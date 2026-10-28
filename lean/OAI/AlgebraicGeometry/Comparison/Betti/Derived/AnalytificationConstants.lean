import OAI.AlgebraicGeometry.Comparison.Betti.Analytification.ConstantSquare
import OAI.AlgebraicGeometry.Comparison.Betti.Derived.SingleSquare

/-! # Analytification Constants -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Derived.AnalytificationConstants

noncomputable section

/-! The analytification mate commutes with the actual derived constant identifications. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y)

theorem analytificationSheafMateIso_inv_constant :
    (Analytic.ResolutionNaturality.schemeAnalyticInverseImage f).map (Analytic.De.analytificationInverseImageConstantIso Y).hom ≫
        (TopologicalSheafPullback.constantPullbackIso (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)).hom =
      (Analytification.MateNaturality.analytificationSheafMateIso f).inv.app (Algebraic.Sheaves.constantComplexSheaf Y) ≫
        (Analytic.De.analytificationInverseImage X).map (Algebraic.Sheaves.inverseImageConstantIso f).hom ≫
          (Analytic.De.analytificationInverseImageConstantIso X).hom := by
  let e := (Analytification.MateNaturality.analytificationSheafMateIso f).app (Algebraic.Sheaves.constantComplexSheaf Y)
  let l := (Analytic.De.analytificationInverseImage X).map (Algebraic.Sheaves.inverseImageConstantIso f).hom ≫
    (Analytic.De.analytificationInverseImageConstantIso X).hom
  let r := (Analytic.ResolutionNaturality.schemeAnalyticInverseImage f).map (Analytic.De.analytificationInverseImageConstantIso Y).hom ≫
    (TopologicalSheafPullback.constantPullbackIso (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)).hom
  have h : l = e.hom ≫ r := Analytification.ConstantSquare.analytificationSheafMateIso_constant f
  exact (e.inv_comp_eq.mpr h).symm

theorem derivedAnalytificationMateIso_constant :
    (Analytic.De.derivedAnalytificationInverseImage X).map (OpenForms.derivedInverseImageConstantIso f).hom ≫
        (Analytic.De.derivedAnalytificationConstantIso X).hom =
      (Analytification.MateNaturality.derivedAnalytificationMateIso f).hom.app
          ((DerivedCategory.singleFunctor (Algebraic.Sheaves.ComplexSheaves Y) 0).obj (Algebraic.Sheaves.constantComplexSheaf Y)) ≫
        (Analytic.ResolutionNaturality.schemeAnalyticInverseImage f).mapDerivedCategory.map (Analytic.De.derivedAnalytificationConstantIso Y).hom ≫
          (Analytic.ResolutionNaturality.schemeAnalyticDerivedConstantIso f).hom := by
  have h := SingleSquare.derivedSingleMap_square.{1, 1, 1, 1}
    (Algebraic.Sheaves.inverseImage f) (Analytic.De.analytificationInverseImage X) (Analytic.De.analytificationInverseImage Y)
    (Analytic.ResolutionNaturality.schemeAnalyticInverseImage f) (Analytification.MateNaturality.analytificationSheafMateIso f)
    (Algebraic.Sheaves.inverseImageConstantIso f).hom (Analytic.De.analytificationInverseImageConstantIso X).hom
    (Analytic.De.analytificationInverseImageConstantIso Y).hom
    (TopologicalSheafPullback.constantPullbackIso (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)).hom
    (analytificationSheafMateIso_inv_constant f)
  let e := (Analytification.MateNaturality.derivedAnalytificationMateIso f).app
    ((DerivedCategory.singleFunctor (Algebraic.Sheaves.ComplexSheaves Y) 0).obj (Algebraic.Sheaves.constantComplexSheaf Y))
  let l := (Analytic.De.derivedAnalytificationInverseImage X).map (OpenForms.derivedInverseImageConstantIso f).hom ≫
    (Analytic.De.derivedAnalytificationConstantIso X).hom
  let r := (Analytic.ResolutionNaturality.schemeAnalyticInverseImage f).mapDerivedCategory.map (Analytic.De.derivedAnalytificationConstantIso Y).hom ≫
    (Analytic.ResolutionNaturality.schemeAnalyticDerivedConstantIso f).hom
  have hh : r = e.inv ≫ l := h
  change l = e.hom ≫ r
  exact e.inv_comp_eq.mp hh.symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.Derived.AnalytificationConstants

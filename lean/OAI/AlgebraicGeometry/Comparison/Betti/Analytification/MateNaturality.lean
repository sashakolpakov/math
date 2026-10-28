import OAI.AlgebraicGeometry.Comparison.Betti.Analytic.ResolutionNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.Analytic.De
import OAI.AlgebraicGeometry.Comparison.Betti.AdjunctionComplexUniqueness
import OAI.AlgebraicGeometry.Comparison.Betti.Derived.FunctorComposition
import OAI.AlgebraicGeometry.Comparison.Betti.Derived.FunctorIso

/-! # Mate Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Analytification.MateNaturality

noncomputable section

/-! The canonical analytification mate on sheaves, complexes, and derived categories. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y)

abbrev schemeAnalyticDirectImage : Smooth.SheafMap.AnalyticComplexSheaves X ⥤ Smooth.SheafMap.AnalyticComplexSheaves Y :=
  TopologicalSheafPullback.sheafDirectImage (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)

instance schemeAnalyticDirectImageAdditive : (schemeAnalyticDirectImage f).Additive :=
  TopologicalSheafPullback.sheafDirectImageAdditive (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)

def schemeAnalyticImageAdjunction : Analytic.ResolutionNaturality.schemeAnalyticInverseImage f ⊣ schemeAnalyticDirectImage f :=
  TopologicalSheafPullback.sheafImageAdjunction (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)

def analytificationSheafMateIso :
    Algebraic.Sheaves.inverseImage f ⋙ Analytic.De.analytificationInverseImage X ≅
      Analytic.De.analytificationInverseImage Y ⋙ Analytic.ResolutionNaturality.schemeAnalyticInverseImage f :=
  ((Algebraic.Sheaves.imageAdjunction f).comp (Analytic.De.analytificationAdjunction X)).leftAdjointUniq
    ((Analytic.De.analytificationAdjunction Y).comp
      (schemeAnalyticImageAdjunction f))

theorem analytificationSheafMateIso_onComplexes (K : CochainComplex (Algebraic.Sheaves.ComplexSheaves Y) ℤ) :
    (NatTrans.mapHomologicalComplex (analytificationSheafMateIso f).hom (ComplexShape.up ℤ)).app K =
      (Analytic.InverseNaturalityInt.analytificationComplexMateIso f).hom.app K := by
  have h := AdjunctionComplexUniqueness.onComplexes_leftAdjointUniq (ComplexShape.up ℤ)
    ((Algebraic.Sheaves.imageAdjunction f).comp (Analytic.De.analytificationAdjunction X))
    ((Analytic.De.analytificationAdjunction Y).comp
      (schemeAnalyticImageAdjunction f)) K
  erw [AdjunctionComplexUniqueness.onComplexes_comp (ComplexShape.up ℤ)
      (Algebraic.Sheaves.imageAdjunction f) (Analytic.De.analytificationAdjunction X),
    AdjunctionComplexUniqueness.onComplexes_comp (ComplexShape.up ℤ)
      (Analytic.De.analytificationAdjunction Y) (schemeAnalyticImageAdjunction f)] at h
  exact h.symm

theorem analytificationSheafMateIso_inv_onComplexes (K : CochainComplex (Algebraic.Sheaves.ComplexSheaves Y) ℤ) :
    (NatTrans.mapHomologicalComplex (analytificationSheafMateIso f).inv (ComplexShape.up ℤ)).app K =
      (Analytic.InverseNaturalityInt.analytificationComplexMateIso f).inv.app K := by
  let a := (NatIso.mapHomologicalComplex (analytificationSheafMateIso f) (ComplexShape.up ℤ)).app K
  let b := (Analytic.InverseNaturalityInt.analytificationComplexMateIso f).app K
  have h : a = b := Iso.ext (analytificationSheafMateIso_onComplexes f K)
  exact congrArg Iso.inv h

def derivedAnalytificationMateIso :
    Algebraic.Sheaves.derivedInverseImage f ⋙ Analytic.De.derivedAnalytificationInverseImage X ≅
      Analytic.De.derivedAnalytificationInverseImage Y ⋙ (Analytic.ResolutionNaturality.schemeAnalyticInverseImage f).mapDerivedCategory :=
  Derived.FunctorComposition.derivedFunctorCompIso.{1, 1, 1} (Algebraic.Sheaves.inverseImage f) (Analytic.De.analytificationInverseImage X) ≪≫
    Derived.FunctorIso.functorIso.{1, 1} (analytificationSheafMateIso f) ≪≫
      (Derived.FunctorComposition.derivedFunctorCompIso.{1, 1, 1} (Analytic.De.analytificationInverseImage Y)
        (Analytic.ResolutionNaturality.schemeAnalyticInverseImage f)).symm

instance derivedAnalytificationMateIsoCommShift :
    NatTrans.CommShift (derivedAnalytificationMateIso f).hom ℤ := by
  change NatTrans.CommShift
    ((Derived.FunctorComposition.derivedFunctorCompIso (Algebraic.Sheaves.inverseImage f) (Analytic.De.analytificationInverseImage X)).hom ≫
      (Derived.FunctorIso.functorIso (analytificationSheafMateIso f)).hom ≫
      (Derived.FunctorComposition.derivedFunctorCompIso (Analytic.De.analytificationInverseImage Y)
        (Analytic.ResolutionNaturality.schemeAnalyticInverseImage f)).inv) ℤ
  infer_instance

end

end OAI.AlgebraicGeometry.Comparison.Betti.Analytification.MateNaturality

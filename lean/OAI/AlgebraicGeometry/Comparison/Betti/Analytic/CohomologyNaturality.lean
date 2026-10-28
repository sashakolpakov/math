import OAI.AlgebraicGeometry.Comparison.Betti.Derived.AnalytificationConstants
import OAI.AlgebraicGeometry.Comparison.Betti.Derived.AnalyticNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.ShiftedHomSquare
import OAI.AlgebraicGeometry.Comparison.Betti.Analytic.Naturality

/-! # Cohomology Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Analytic.CohomologyNaturality

noncomputable section

/-! Naturality of the original algebraic-to-analytic and integral de Rham–Betti maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y)

theorem algebraicDeRhamPullback_transport (n : ℕ) (a : Algebraic.Sheaves.algebraicDeRham Y n) :
    OpenForms.algebraicDeRhamPullback f n a =
      ShiftedHomSquare.transport (Algebraic.Sheaves.derivedInverseImage f) (OpenForms.derivedInverseImageConstantIso f)
        (OpenForms.derivedDeRhamPullback f) a := by
  change (OpenForms.derivedInverseImageConstantIso f).inv ≫ (Algebraic.Sheaves.derivedInverseImage f).map a ≫
      ((Algebraic.Sheaves.derivedInverseImage f).commShiftIso (n : ℤ)).hom.app _ ≫
        (OpenForms.derivedDeRhamPullback f)⟦(n : ℤ)⟧' = _
  simp only [ShiftedHomSquare.transport, ShiftedHom.map, Category.assoc]

theorem analyticConstantPullback_transport (n : ℕ) (a : De.analyticConstantCohomology Y n) :
    Naturality.analyticConstantPullback f n a =
      ShiftedHomSquare.transport (ResolutionNaturality.schemeAnalyticInverseImage f).mapDerivedCategory
        (ResolutionNaturality.schemeAnalyticDerivedConstantIso f) (ResolutionNaturality.schemeAnalyticDerivedConstantIso f).hom a := rfl

variable [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]

theorem algebraicToAnalyticCohomologyMap_transport (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [IsIntegral Z.left] [Smooth Z.hom] (n : ℕ) (a : Algebraic.Sheaves.algebraicDeRham Z n) :
    De.algebraicToAnalyticCohomologyMap Z n a =
      ShiftedHomSquare.transport (De.derivedAnalytificationInverseImage Z) (De.derivedAnalytificationConstantIso Z)
        (De.derivedAlgebraicToAnalyticConstant Z) a := by
  change (De.derivedAnalytificationConstantIso Z).inv ≫ (De.derivedAnalytificationInverseImage Z).map a ≫
      ((De.derivedAnalytificationInverseImage Z).commShiftIso (n : ℤ)).hom.app _ ≫
        (De.derivedAlgebraicToAnalyticConstant Z)⟦(n : ℤ)⟧' = _
  simp only [ShiftedHomSquare.transport, ShiftedHom.map, Category.assoc]

theorem algebraicToAnalyticCohomologyMap_naturality (n : ℕ) :
    OpenForms.algebraicDeRhamPullback f n ≫ De.algebraicToAnalyticCohomologyMap X n =
      De.algebraicToAnalyticCohomologyMap Y n ≫ Naturality.analyticConstantPullback f n := by
  ext a
  change De.algebraicToAnalyticCohomologyMap X n (OpenForms.algebraicDeRhamPullback f n a) =
    Naturality.analyticConstantPullback f n (De.algebraicToAnalyticCohomologyMap Y n a)
  erw [algebraicToAnalyticCohomologyMap_transport X n, analyticConstantPullback_transport f n,
    algebraicDeRhamPullback_transport f n, algebraicToAnalyticCohomologyMap_transport Y n]
  exact ShiftedHomSquare.transport_square
    (Algebraic.Sheaves.derivedInverseImage f) (De.derivedAnalytificationInverseImage X)
    (De.derivedAnalytificationInverseImage Y) (ResolutionNaturality.schemeAnalyticInverseImage f).mapDerivedCategory
    (Analytification.MateNaturality.derivedAnalytificationMateIso f)
    (OpenForms.derivedInverseImageConstantIso f) (De.derivedAnalytificationConstantIso X)
    (De.derivedAnalytificationConstantIso Y) (ResolutionNaturality.schemeAnalyticDerivedConstantIso f)
    (OpenForms.derivedDeRhamPullback f) (De.derivedAlgebraicToAnalyticConstant X)
    (De.derivedAlgebraicToAnalyticConstant Y) (ResolutionNaturality.schemeAnalyticDerivedConstantIso f).hom
    (Derived.AnalytificationConstants.derivedAnalytificationMateIso_constant f) (Derived.AnalyticNaturality.derivedAlgebraicToAnalyticConstant_naturality f) a

variable [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]

theorem algebraicDeRhamBettiMap_naturality (n : ℕ) :
    OpenForms.algebraicDeRhamPullback f n ≫ Algebraic.Map.algebraicDeRhamBettiMap X n =
      Algebraic.Map.algebraicDeRhamBettiMap Y n ≫ Algebraic.Sheaves.bettiPullback f n := by
  unfold Algebraic.Map.algebraicDeRhamBettiMap
  rw [← Category.assoc, algebraicToAnalyticCohomologyMap_naturality,
    Category.assoc, Naturality.analyticConstantBettiIso_naturality, Category.assoc]

end

end OAI.AlgebraicGeometry.Comparison.Betti.Analytic.CohomologyNaturality

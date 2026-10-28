import OAI.Analysis.HodgeTheory.Decomposition.CoordinateLp

/-! # Coefficient Linearity -/

namespace OAI.Analysis.HodgeTheory.Decomposition.CoefficientLinearity.Constructions

noncomputable section

/-! Complex linearity of the genuine chart coefficient maps and of their
zero extensions. -/

open scoped _root_.Manifold

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ)

def euclideanChartCoefficientLinear :
    DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n →ₗ[ℂ]
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) where
  toFun := EuclideanForms.Constructions.euclideanChartCoefficients V e n
  map_add' a b := by
    funext z
    change EuclideanForms.Constructions.euclideanChartCoefficients V e n (a + b) z =
      EuclideanForms.Constructions.euclideanChartCoefficients V e n a z + EuclideanForms.Constructions.euclideanChartCoefficients V e n b z
    rw [EuclideanForms.Constructions.euclideanChartCoefficients_eq_analytic, EuclideanForms.Constructions.euclideanChartCoefficients_eq_analytic,
      EuclideanForms.Constructions.euclideanChartCoefficients_eq_analytic, DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_add, Pi.add_apply, map_add]
  map_smul' c a := by
    funext z
    change EuclideanForms.Constructions.euclideanChartCoefficients V e n (c • a) z = c • EuclideanForms.Constructions.euclideanChartCoefficients V e n a z
    rw [EuclideanForms.Constructions.euclideanChartCoefficients_eq_analytic, EuclideanForms.Constructions.euclideanChartCoefficients_eq_analytic,
      DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_smul, Pi.smul_apply, map_smul]

def supportedCoefficientLinear :
    DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n →ₗ[ℂ]
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) where
  toFun := SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n
  map_add' a b := by
    funext z
    change SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n (a + b) z =
      SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n a z + SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n b z
    by_cases hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e
    · rw [SupportedCoordinates.Constructions.supportedEuclideanCoefficients_eq V e n (a + b) hz,
        SupportedCoordinates.Constructions.supportedEuclideanCoefficients_eq V e n a hz, SupportedCoordinates.Constructions.supportedEuclideanCoefficients_eq V e n b hz]
      exact congrFun ((euclideanChartCoefficientLinear V e n).map_add a b) z
    · simp only [SupportedCoordinates.Constructions.supportedEuclideanCoefficients, Set.indicator_of_notMem hz, add_zero]
  map_smul' c a := by
    funext z
    change SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n (c • a) z = c • SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n a z
    by_cases hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e
    · rw [SupportedCoordinates.Constructions.supportedEuclideanCoefficients_eq V e n (c • a) hz,
        SupportedCoordinates.Constructions.supportedEuclideanCoefficients_eq V e n a hz]
      exact congrFun ((euclideanChartCoefficientLinear V e n).map_smul c a) z
    · simp only [SupportedCoordinates.Constructions.supportedEuclideanCoefficients, Set.indicator_of_notMem hz, smul_zero]

end

end OAI.Analysis.HodgeTheory.Decomposition.CoefficientLinearity.Constructions

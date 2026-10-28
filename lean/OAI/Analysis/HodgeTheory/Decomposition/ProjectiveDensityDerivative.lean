import OAI.Analysis.HodgeTheory.Decomposition.MetricDensityDerivative
import OAI.Analysis.HodgeTheory.Decomposition.ProjectiveConnectionSmooth

/-! # Projective Density Derivative -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ProjectiveDensityDerivative.Constructions

noncomputable section

/-! The actual projective metric-volume derivative in its genuine charts. -/

open scoped ContDiff

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem projectiveMetricDensity_derivative {z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (u : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    fderiv ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e) z u = AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z *
      (LinearMap.toMatrix (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
        (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
          (ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e z u).toLinearMap).trace :=
  MetricDensityDerivative.Constructions.metricDensity_fderiv_connection _ _
    (((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he).contDiffAt
      ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)).differentiableAt (by simp))
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he hz) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz)
    u (ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e z u) (ProjectiveConnection.Constructions.projectiveConnectionCoefficient_metric V e he hz u)

end

end OAI.Analysis.HodgeTheory.Decomposition.ProjectiveDensityDerivative.Constructions

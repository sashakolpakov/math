import OAI.AlgebraicGeometry.DivisorClass.Chern.CovectorTensorProjection
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.TensorIntegration

/-! # Rough Energy Density -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The derivative term in the original rough Laplacian integration identity is a nonnegative tensor energy density. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveRoughEnergyDensity_nonneg (n : ℕ) (i : V.analyticSpace)
    (a : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) n)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    let B := ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z
    let M := Line.ConnectionSymbols.lineCovectorConnectionDerivative n (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i) a z
    let N := Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) n) M
    0 ≤ ((ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z : ℂ) * h.projectiveWeightChart V e i z *
      (∑ j, Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B (N (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord j).toContinuousLinearMap)) (M (b j)))).re := by
  have hp := CovectorTensorProjection.covectorTensorAntiProjection_nonneg
    (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z)
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he hz.1) (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz.1)
    (Analysis.HodgeTheory.Decomposition.EuclideanMetricDerivative.Constructions.projectiveEuclideanMetric_J_skew V e he hz.1)
    (Line.ConnectionSymbols.lineCovectorConnectionDerivative n (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i) a z)
  dsimp only at hp ⊢
  simp only [CovectorTensorAlgebra.covectorTensorMetricPair] at hp
  rw [h.projectiveWeightChart_apply V e i hz]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, add_zero, sub_zero]
  exact mul_nonneg (mul_nonneg (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity_pos V e he hz.1).le (h.positive i _).le) hp

end

end OAI.AlgebraicGeometry.DivisorClass.Chern

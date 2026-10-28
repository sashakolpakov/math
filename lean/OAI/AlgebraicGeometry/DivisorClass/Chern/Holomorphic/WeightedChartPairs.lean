import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.GlobalFrameForms
import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveLine.MetricOperator
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.VariableMetricIntegral

/-! # Weighted Chart Pairs -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! Exact comparison of native line metric matrices with original manifold and bundle pairings. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (i : V.analyticSpace) (n : ℕ)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveWeightedFormOperator_manifoldPair
    (a b : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    inner ℝ (h.projectiveWeightedFormOperator V e i n z (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e n a z))
      (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e n b z) =
        ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z * (((h.weight i ⟨Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z, hz.2⟩ : ℂ) *
          Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a b (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z)).re) := by
  rw [HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveWeightedFormOperator, _root_.smul_apply, real_inner_smul_left,
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients_weighted_inner V e he n a b z hz.1, h.projectiveWeightChart_apply V e i hz]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse]
  ring

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.globalFormPair_coordinates
    (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    inner ℝ (h.projectiveWeightedFormOperator V e i n z
      (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e n (Holomorphic.GlobalFrameForms.holomorphicLineGlobalFrame u i n a).extension z))
      (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e n (Holomorphic.GlobalFrameForms.holomorphicLineGlobalFrame u i n b).extension z) =
        ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z * (h.globalFormPair V n a b (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z)).re := by
  rw [h.projectiveWeightedFormOperator_manifoldPair V e he i n _ _ hz,
    h.globalFormPair_inFrame V n a b i (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) hz.2,
    Projective.CovectorPair.projectiveFormPointPair_eq_tangentPair,
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply _ ⟨Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z, hz.2⟩,
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply _ ⟨Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z, hz.2⟩,
    Holomorphic.GlobalFrameForms.holomorphicLineGlobalFrame_apply, Holomorphic.GlobalFrameForms.holomorphicLineGlobalFrame_apply]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern

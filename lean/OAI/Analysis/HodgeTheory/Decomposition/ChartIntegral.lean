import OAI.Analysis.HodgeTheory.Decomposition.EuclideanForms
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Chart Integral -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ChartIntegral.Constructions

noncomputable section

/-! Signed and vector-valued integration against the actual metric volume in
charts. These identities connect coordinate integration by parts to L². -/

open scoped _root_.Manifold ENNReal
open _root_.MeasureTheory

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem projectiveChartMeasure_integral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (h : V.analyticSpace → F) (hh : AEStronglyMeasurable h (MeasureVolume.Constructions.projectiveChartMeasure V e)) :
    (∫ x, h x ∂ MeasureVolume.Constructions.projectiveChartMeasure V e) =
      ∫ z in AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e,
        AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z • h (MeasureVolume.Constructions.chartCoordinateInverse V e z) := by
  rw [MeasureVolume.Constructions.projectiveChartMeasure, integral_map (MeasureVolume.Constructions.chartCoordinateInverse_aemeasurable V e) hh]
  rw [MeasureVolume.Constructions.chartMetricDensityMeasure, integral_withDensity_eq_integral_toReal_smul₀
    (MeasureVolume.Constructions.chartMetricDensity_aemeasurable V e he) (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply setIntegral_congr_fun (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.measurableSet
  intro z hz
  dsimp only
  rw [ENNReal.toReal_ofReal (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity_pos V e he hz).le]

theorem projectiveMetricVolume_integral_chart {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (h : V.analyticSpace → F) (hh : AEStronglyMeasurable h (MeasureVolume.Constructions.projectiveChartMeasure V e))
    (hs : ∀ x, x ∉ e.source → h x = 0) :
    (∫ x, h x ∂ MeasureVolume.Constructions.projectiveMetricVolume V) =
      ∫ z in AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e,
        AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z • h (MeasureVolume.Constructions.chartCoordinateInverse V e z) := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hs,
    MeasureVolume.Constructions.projectiveMetricVolume_restrict V e he,
    setIntegral_eq_integral_of_forall_compl_eq_zero hs]
  exact projectiveChartMeasure_integral V e he h hh

end

end OAI.Analysis.HodgeTheory.Decomposition.ChartIntegral.Constructions

import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalMetricMeasure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Metric Bochner Integration -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricBochnerIntegration.CM.Construction

noncomputable section

/-! The actual Bochner integral in a projective metric chart is the
Euclidean integral weighted by the genuine metric volume density. -/

open _root_.MeasureTheory Set
open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem varietyMetricChartMeasure_integral (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (f : V.analyticSpace → F) (hf : AEStronglyMeasurable f (MetricChartMeasure.CM.Construction.varietyMetricChartMeasure V e)) :
    (∫ x, f x ∂ MetricChartMeasure.CM.Construction.varietyMetricChartMeasure V e) =
      ∫ z in (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)),
        Metric.CM.Construction.varietyMetricDensity V e z • f (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) := by
  have hρ : Measurable (fun z : EuclideanMetric.CM.Construction.varietyEuclideanDomain V e => ENNReal.ofReal (Metric.CM.Construction.varietyMetricDensity V e z.val)) := by
    have hcont : Continuous (fun z : EuclideanMetric.CM.Construction.varietyEuclideanDomain V e => Metric.CM.Construction.varietyMetricDensity V e z.val) :=
      (Metric.CM.Construction.varietyMetricDensity_smooth V e he).continuousOn.comp_continuous continuous_subtype_val (fun z => z.property)
    exact (ENNReal.continuous_ofReal.comp hcont).measurable
  rw [MetricChartMeasure.CM.Construction.varietyMetricChartMeasure] at hf ⊢
  rw [integral_map (MetricChartMeasure.CM.Construction.varietyEuclideanChartPoint_continuous V e).measurable.aemeasurable hf,
    integral_withDensity_eq_integral_toReal_smul hρ
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  calc
    _ = ∫ z : EuclideanMetric.CM.Construction.varietyEuclideanDomain V e,
        Metric.CM.Construction.varietyMetricDensity V e z.val • f (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z.val))
          ∂(volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)).comap (Subtype.val : EuclideanMetric.CM.Construction.varietyEuclideanDomain V e → EuclideanMetric.CM.Construction.varietyEuclideanModel V) := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro z
      dsimp only
      rw [ENNReal.toReal_ofReal (Metric.CM.Construction.varietyMetricDensity_pos V e he z.property).le]
      rfl
    _ = _ := integral_subtype_comap (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.measurableSet
      (fun z => Metric.CM.Construction.varietyMetricDensity V e z • f (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)))

theorem varietyMetricMeasure_integral_chart (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (f : V.analyticSpace → F) (hf : AEStronglyMeasurable f (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V)) :
    (∫ x in e.source, f x ∂ GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) =
      ∫ z in (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)),
        Metric.CM.Construction.varietyMetricDensity V e z • f (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) := by
  rw [GlobalMetricMeasure.CM.Construction.varietyMetricMeasure_restrict_chart V e he]
  apply varietyMetricChartMeasure_integral V e he f
  rw [← GlobalMetricMeasure.CM.Construction.varietyMetricMeasure_restrict_chart V e he]
  exact hf.restrict

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricBochnerIntegration.CM.Construction

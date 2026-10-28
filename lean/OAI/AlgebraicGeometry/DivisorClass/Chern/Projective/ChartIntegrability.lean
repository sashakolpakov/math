import OAI.Analysis.HodgeTheory.Decomposition.ChartIntegral

/-! # Chart Integrability -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.ChartIntegrability

noncomputable section

section

/-! Integrable original global functions remain integrable against the actual chart density. -/

open _root_.MeasureTheory
open scoped _root_.Manifold
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.Analysis.HodgeTheory.Decomposition.ChartIntegral.Constructions

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem projectiveChartMeasure_eq_restrict :
    Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.projectiveChartMeasure V e = (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.projectiveMetricVolume V).restrict e.source := by
  rw [Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.projectiveMetricVolume_restrict V e he]
  exact (Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.projectiveChartMeasure_compl_source V e))).symm

theorem projective_chart_density_integrable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : V.analyticSpace → F) (hf : Integrable f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.projectiveMetricVolume V)) :
    IntegrableOn (fun z => ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z • f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z))
      (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) := by
  have hc : Integrable f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.projectiveChartMeasure V e) := by
    rw [projectiveChartMeasure_eq_restrict V e he]
    exact hf.restrict
  have hm : Integrable (fun z => f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z)) (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartMetricDensityMeasure V e) :=
    hc.comp_aemeasurable (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse_aemeasurable V e)
  have hw := (integrable_withDensity_iff_integrable_smul₀'
    (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartMetricDensity_aemeasurable V e he)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mp hm
  apply hw.congr
  filter_upwards [ae_restrict_mem (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.measurableSet] with z hz
  rw [ENNReal.toReal_ofReal (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity_pos V e he hz).le]

end

/-! A nonnegative original chart integral over any coordinate subset is bounded by the original global integral. -/

open _root_.MeasureTheory
open scoped _root_.Manifold
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.Analysis.HodgeTheory.Decomposition.ChartIntegral.Constructions

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem projective_chart_integral_le (f : V.analyticSpace → ℝ)
    (hf : Integrable f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.projectiveMetricVolume V)) (hn : ∀ x, 0 ≤ f x)
    {S : Set (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hS : S ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    (∫ z in S, ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z * f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z)) ≤
      ∫ x, f x ∂ Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.projectiveMetricVolume V := by
  have hc : Integrable f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.projectiveChartMeasure V e) := by
    rw [projectiveChartMeasure_eq_restrict V e he]
    exact hf.restrict
  have hi : IntegrableOn (fun z => ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z * f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z))
      (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) := by
    simpa only [smul_eq_mul] using projective_chart_density_integrable V e he f hf
  calc
    _ ≤ ∫ z in ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e,
        ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z * f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) := by
      apply setIntegral_mono_set hi _ (Filter.Eventually.of_forall hS)
      filter_upwards [ae_restrict_mem (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.measurableSet] with z hz
      exact mul_nonneg (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity_pos V e he hz).le (hn _)
    _ = ∫ x, f x ∂ Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.projectiveChartMeasure V e := by
      simpa only [smul_eq_mul] using (Analysis.HodgeTheory.Decomposition.ChartIntegral.Constructions.projectiveChartMeasure_integral V e he f hc.aestronglyMeasurable).symm
    _ ≤ _ := by
      rw [projectiveChartMeasure_eq_restrict V e he]
      exact setIntegral_le_integral hf (Filter.Eventually.of_forall hn)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.ChartIntegrability

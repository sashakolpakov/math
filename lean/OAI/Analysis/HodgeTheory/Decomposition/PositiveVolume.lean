import OAI.Analysis.HodgeTheory.Decomposition.MeasureVolume
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Positive Volume -/

namespace OAI.Analysis.HodgeTheory.Decomposition.PositiveVolume.Constructions

noncomputable section

/-! Full support of the actual metric volume. This ensures that the L²
pairing of continuous smooth forms will be positive definite. -/

open scoped _root_.Manifold ENNReal
open _root_.MeasureTheory Set

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]

omit [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace] in
theorem chartMetricDensity_integral_ne_zero
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {K : Set (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hK : MeasurableSet K)
    (hKU : K ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (hvol : volume K ≠ 0) :
    (∫⁻ z in K, ENNReal.ofReal (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z)) ≠ 0 := by
  have hm : AEMeasurable (fun z => ENNReal.ofReal (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z)) (volume.restrict K) :=
    (ENNReal.continuous_ofReal.comp_continuousOn
    ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity_smooth V e he).continuousOn.mono hKU)).aemeasurable hK
  intro hz
  have hae := (setLIntegral_eq_zero_iff' hK hm).mp hz
  apply hvol
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hae] with z hz
  intro hzK
  have hp : 0 < ENNReal.ofReal (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z) :=
    ENNReal.ofReal_pos.mpr (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity_pos V e he (hKU hzK))
  exact hp.ne' (hz hzK)

/-- The projective metric volume is positive on every nonempty open subset. -/
instance projectiveMetricVolume_openPos : Measure.IsOpenPosMeasure (MeasureVolume.Constructions.projectiveMetricVolume V) where
  open_pos s hs hne := by
    obtain ⟨x, hx⟩ := hne
    let e := chartAt V.analyticModel x
    have he := chart_mem_atlas V.analyticModel x
    have hex := mem_chart_source V.analyticModel x
    let t := s ∩ e.source
    have ht : IsOpen t := hs.inter e.open_source
    have hte : t ⊆ e.source := inter_subset_right
    have hK : IsOpen (MeasureVolume.Constructions.chartCoordinateSet V e t) :=
      (MeasureVolume.Constructions.chartCoordinateInverse_continuousOn V e).isOpen_inter_preimage
        (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen ht
    have hKn : (MeasureVolume.Constructions.chartCoordinateSet V e t).Nonempty := by
      refine ⟨MeasureVolume.Constructions.chartCoordinateForward V e x, MeasureVolume.Constructions.chartCoordinateForward_mem V e x hex, ?_⟩
      change MeasureVolume.Constructions.chartCoordinateInverse V e (MeasureVolume.Constructions.chartCoordinateForward V e x) ∈ t
      rw [MeasureVolume.Constructions.chartCoordinateInverse_forward V e x hex]
      exact ⟨hx, hex⟩
    have htpos : MeasureVolume.Constructions.projectiveMetricVolume V t ≠ 0 := by
      rw [MeasureVolume.Constructions.projectiveMetricVolume_apply_chart V e he ht.measurableSet hte,
        MeasureVolume.Constructions.projectiveChartMeasure_apply V e he ht.measurableSet]
      exact chartMetricDensity_integral_ne_zero V e he hK.measurableSet (fun _ hz => hz.1)
        (hK.measure_ne_zero volume hKn)
    intro hz
    apply htpos
    exact measure_mono_null (show t ⊆ s from inter_subset_left) hz

end

end OAI.Analysis.HodgeTheory.Decomposition.PositiveVolume.Constructions

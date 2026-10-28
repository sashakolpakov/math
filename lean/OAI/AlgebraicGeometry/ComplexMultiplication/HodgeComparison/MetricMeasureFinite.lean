import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalMetricMeasure
import OAI.AlgebraicGeometry.CycleClass.Geometric.CompactChartCover
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Metric Measure Finite -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricMeasureFinite.CM.Construction

noncomputable section

/-! Finiteness of the actual global metric measure follows from compact
coordinate pieces and continuity of the genuine metric densities. -/

open _root_.MeasureTheory Set
open scoped ENNReal _root_.Manifold

theorem varietyMetricChartCoordinates_eq_image (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) {S : Set V.analyticSpace}
    (hS : S ⊆ e.source) :
    MetricChartMeasure.CM.Construction.varietyMetricChartCoordinates V e S =
      (fun x => (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x)) '' S := by
  apply Subset.antisymm
  · intro z hz
    have h := (MetricChartMeasure.CM.Construction.mem_varietyMetricChartCoordinates V e S z).mp hz
    refine ⟨e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z), h.2, ?_⟩
    dsimp only
    rw [e.right_inv h.1, ContinuousLinearEquiv.symm_apply_apply]
  · rintro _ ⟨x, hx, rfl⟩
    apply (MetricChartMeasure.CM.Construction.mem_varietyMetricChartCoordinates V e S _).mpr
    refine ⟨?_, ?_⟩
    · change EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x)) ∈ e.target
      rw [ContinuousLinearEquiv.apply_symm_apply]
      exact e.map_source (hS hx)
    · rw [ContinuousLinearEquiv.apply_symm_apply, e.left_inv (hS hx)]
      exact hx

theorem varietyMetricChartCoordinates_isCompact (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) {S : Set V.analyticSpace}
    (hS : IsCompact S) (hSe : S ⊆ e.source) : IsCompact (MetricChartMeasure.CM.Construction.varietyMetricChartCoordinates V e S) := by
  rw [varietyMetricChartCoordinates_eq_image V e hSe]
  exact hS.image_of_continuousOn
    ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm.continuous.comp_continuousOn (e.continuousOn.mono hSe))

theorem varietyMetricMeasure_compact_in_chart_lt_top (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {S : Set V.analyticSpace} (hS : IsCompact S) (hSe : S ⊆ e.source) :
    GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V S < ∞ := by
  rw [← Measure.restrict_eq_self (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) hSe,
    GlobalMetricMeasure.CM.Construction.varietyMetricMeasure_restrict_chart V e he, MetricChartMeasure.CM.Construction.varietyMetricChartMeasure_apply V e hS.measurableSet]
  have hK := varietyMetricChartCoordinates_isCompact V e hS hSe
  have hKU : MetricChartMeasure.CM.Construction.varietyMetricChartCoordinates V e S ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e :=
    fun z hz => ((MetricChartMeasure.CM.Construction.mem_varietyMetricChartCoordinates V e S z).mp hz).1
  have hInt : IntegrableOn (Metric.CM.Construction.varietyMetricDensity V e) (MetricChartMeasure.CM.Construction.varietyMetricChartCoordinates V e S) :=
    ((Metric.CM.Construction.varietyMetricDensity_smooth V e he).continuousOn.mono hKU).integrableOn_compact hK
  exact hInt.lintegral_lt_top

theorem varietyMetricMeasure_univ_lt_top (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V univ < ∞ := by
  obtain ⟨centers, radius, pieces, hcover, hpieces⟩ :=
    CycleClass.Geometric.CompactChartCover.Cycles.exists_compact_chart_decomposition V.analyticModel
      (isCompact_univ : IsCompact (univ : Set V.analyticSpace))
  rw [hcover]
  apply (measure_biUnion_finset_le centers pieces).trans_lt
  apply ENNReal.sum_lt_top.mpr
  intro x hx
  obtain ⟨_, hPc, _, hPchart, _, _⟩ := hpieces x hx
  exact varietyMetricMeasure_compact_in_chart_lt_top V (chartAt V.analyticModel x)
    (chart_mem_atlas V.analyticModel x) hPc
    (hPchart.trans (CycleClass.Geometric.CompactChartCover.Cycles.chartClosedBallDomain_subset_source V.analyticModel x (radius x)))

instance varietyMetricMeasure_isFinite (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    IsFiniteMeasure (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) := ⟨varietyMetricMeasure_univ_lt_top V⟩

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricMeasureFinite.CM.Construction

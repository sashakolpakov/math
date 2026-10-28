import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricChartMeasure
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MeasureGluing
import OAI.Topology.Euclidean.FiniteChartCover

/-! # Global Metric Measure -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction

noncomputable section

/-! A genuine global Borel measure for the projective metric, whose
restriction to every atlas chart is its density-weighted Euclidean measure. -/

open _root_.MeasureTheory Set
open scoped _root_.Manifold

structure MetricChartCover (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) where
  size : ℕ
  chart : Fin size → OpenPartialHomeomorph V.analyticSpace V.analyticModel
  chart_mem : ∀ i, chart i ∈ atlas V.analyticModel V.analyticSpace
  covers : ⋃ i, (chart i).source = univ

theorem metricChartCover_nonempty (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : Nonempty (MetricChartCover V) := by
  classical
  obtain ⟨s, hs⟩ := Topology.Euclidean.FiniteChartCover.Globalization.exists_finite_chart_cover V.analyticModel (M := V.analyticSpace)
  refine ⟨⟨Fintype.card s, (fun i => chartAt V.analyticModel ((Fintype.equivFin s).symm i).val),
    (fun i => chart_mem_atlas V.analyticModel _), ?_⟩⟩
  apply eq_univ_of_forall
  intro x
  have hx : x ∈ ⋃ y ∈ s, (chartAt V.analyticModel y).source := by rw [hs]; trivial
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp hx
  refine mem_iUnion.mpr ⟨Fintype.equivFin s ⟨y, hy⟩, ?_⟩
  simpa only [Equiv.symm_apply_apply] using hxy

def projectiveMetricChartCover (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : MetricChartCover V :=
  Classical.choice (metricChartCover_nonempty V)

def varietyMetricMeasure (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : Measure V.analyticSpace :=
  MeasureGluing.CM.Construction.gluedChartMeasure (fun i => ((projectiveMetricChartCover V).chart i).source)
    (fun i => MetricChartMeasure.CM.Construction.varietyMetricChartMeasure V ((projectiveMetricChartCover V).chart i))

theorem varietyMetricMeasure_restrict_cover (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (i : Fin (projectiveMetricChartCover V).size) :
    (varietyMetricMeasure V).restrict ((projectiveMetricChartCover V).chart i).source =
      MetricChartMeasure.CM.Construction.varietyMetricChartMeasure V ((projectiveMetricChartCover V).chart i) := by
  let C := projectiveMetricChartCover V
  change (MeasureGluing.CM.Construction.gluedChartMeasure (fun i => (C.chart i).source)
    (fun i => MetricChartMeasure.CM.Construction.varietyMetricChartMeasure V (C.chart i))).restrict (C.chart i).source = _
  rw [MeasureGluing.CM.Construction.gluedChartMeasure_restrict (fun i => (C.chart i).source)
    (fun i => MetricChartMeasure.CM.Construction.varietyMetricChartMeasure V (C.chart i))
    (fun i => (C.chart i).open_source.measurableSet) C.covers
    (fun i j => MetricChartMeasure.CM.Construction.varietyMetricChartMeasure_restrict_overlap V (C.chart i) (C.chart j) (C.chart_mem i) (C.chart_mem j)) i,
    MetricChartMeasure.CM.Construction.varietyMetricChartMeasure_restrict_source]

theorem supported_overlap_restrictions_eq {X : Type*} [MeasurableSpace X]
    {U W : Set X} (hU : MeasurableSet U) (hW : MeasurableSet W)
    (μ ν : Measure X) (hμ : μ.restrict U = μ) (hν : ν.restrict W = ν)
    (hcompat : μ.restrict (U ∩ W) = ν.restrict (U ∩ W)) :
    μ.restrict W = ν.restrict U := by
  calc
    _ = (μ.restrict U).restrict W := by rw [hμ]
    _ = μ.restrict (W ∩ U) := Measure.restrict_restrict hW
    _ = μ.restrict (U ∩ W) := by rw [inter_comm]
    _ = ν.restrict (U ∩ W) := hcompat
    _ = (ν.restrict W).restrict U := (Measure.restrict_restrict hU).symm
    _ = _ := by rw [hν]

/-- The global measure has the actual metric density in every chart, including
charts outside the finite family used in its construction. -/
theorem varietyMetricMeasure_restrict_chart (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) :
    (varietyMetricMeasure V).restrict e.source = MetricChartMeasure.CM.Construction.varietyMetricChartMeasure V e := by
  let C := projectiveMetricChartCover V
  apply Measure.ext_of_iUnion_eq_univ C.covers
  intro i
  rw [Measure.restrict_comm (C.chart i).open_source.measurableSet,
    varietyMetricMeasure_restrict_cover]
  exact supported_overlap_restrictions_eq (C.chart i).open_source.measurableSet e.open_source.measurableSet
    (MetricChartMeasure.CM.Construction.varietyMetricChartMeasure V (C.chart i)) (MetricChartMeasure.CM.Construction.varietyMetricChartMeasure V e)
    (MetricChartMeasure.CM.Construction.varietyMetricChartMeasure_restrict_source V (C.chart i))
    (MetricChartMeasure.CM.Construction.varietyMetricChartMeasure_restrict_source V e)
    (MetricChartMeasure.CM.Construction.varietyMetricChartMeasure_restrict_overlap V (C.chart i) e (C.chart_mem i) he)

theorem varietyMetricMeasure_unique (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (μ : Measure V.analyticSpace)
    (hμ : ∀ e : OpenPartialHomeomorph V.analyticSpace V.analyticModel,
      e ∈ atlas V.analyticModel V.analyticSpace → μ.restrict e.source = MetricChartMeasure.CM.Construction.varietyMetricChartMeasure V e) :
    μ = varietyMetricMeasure V := by
  let C := projectiveMetricChartCover V
  apply Measure.ext_of_iUnion_eq_univ C.covers
  intro i
  rw [hμ (C.chart i) (C.chart_mem i), varietyMetricMeasure_restrict_cover]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction

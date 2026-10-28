import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricMeasureFinite
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Chart Measure -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartMeasure.CM.Construction

noncomputable section

section

/-! The actual projective metric measure is positive on every nonempty open
set. Consequently it detects equality of continuous functions. -/

open _root_.MeasureTheory Set
open scoped ENNReal _root_.Manifold

theorem varietyMetricChartCoordinates_isOpen (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) {S : Set V.analyticSpace}
    (hS : IsOpen S) (hSe : S ⊆ e.source) : IsOpen (MetricChartMeasure.CM.Construction.varietyMetricChartCoordinates V e S) := by
  rw [MetricMeasureFinite.CM.Construction.varietyMetricChartCoordinates_eq_image V e hSe]
  have h := (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm.toHomeomorph.isOpenMap (e '' S)
    (e.isOpen_image_of_subset_source hS hSe)
  simpa only [image_image, ContinuousLinearEquiv.coe_toHomeomorph] using h

theorem varietyMetricChartMeasure_open_pos (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {S : Set V.analyticSpace} (hS : IsOpen S) (hSe : S ⊆ e.source) (hne : S.Nonempty) :
    0 < MetricChartMeasure.CM.Construction.varietyMetricChartMeasure V e S := by
  rw [MetricChartMeasure.CM.Construction.varietyMetricChartMeasure_apply V e hS.measurableSet]
  let N := MetricChartMeasure.CM.Construction.varietyMetricChartCoordinates V e S
  have hN : IsOpen N := varietyMetricChartCoordinates_isOpen V e hS hSe
  have hNne : N.Nonempty := by
    rw [show N = (fun x => (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x)) '' S from
      MetricMeasureFinite.CM.Construction.varietyMetricChartCoordinates_eq_image V e hSe]
    exact hne.image _
  have hNU : N ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e :=
    fun z hz => ((MetricChartMeasure.CM.Construction.mem_varietyMetricChartCoordinates V e S z).mp hz).1
  have hρ : AEMeasurable (fun z => ENNReal.ofReal (Metric.CM.Construction.varietyMetricDensity V e z))
      ((volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)).restrict N) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((Metric.CM.Construction.varietyMetricDensity_smooth V e he).continuousOn.mono hNU).aestronglyMeasurable hN.measurableSet).aemeasurable
  apply pos_iff_ne_zero.mpr
  intro hzero
  have hz := (lintegral_eq_zero_iff' hρ).mp hzero
  have hfalse : ∀ᵐ z ∂(volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)).restrict N, False := by
    filter_upwards [hz, ae_restrict_mem hN.measurableSet] with z hval hmem
    exact (ENNReal.ofReal_pos.mpr (Metric.CM.Construction.varietyMetricDensity_pos V e he (hNU hmem))).ne' hval
  have hmeasure : (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) N = 0 := by
    simpa only [ae_iff, not_false_eq_true, Set.ofPred_true,
      Measure.restrict_apply MeasurableSet.univ, univ_inter] using hfalse
  exact (hN.measure_pos volume hNne).ne' hmeasure

theorem varietyMetricMeasure_open_pos (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {S : Set V.analyticSpace} (hS : IsOpen S) (hne : S.Nonempty) : 0 < GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V S := by
  obtain ⟨x, hx⟩ := hne
  let e := chartAt V.analyticModel x
  have hT : IsOpen (S ∩ e.source) := hS.inter e.open_source
  have hTne : (S ∩ e.source).Nonempty := ⟨x, hx, mem_chart_source V.analyticModel x⟩
  have hpos : 0 < GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V (S ∩ e.source) := by
    rw [← Measure.restrict_eq_self (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) inter_subset_right,
      GlobalMetricMeasure.CM.Construction.varietyMetricMeasure_restrict_chart V e (chart_mem_atlas V.analyticModel x)]
    exact varietyMetricChartMeasure_open_pos V e (chart_mem_atlas V.analyticModel x)
      hT inter_subset_right hTne
  exact hpos.trans_le (measure_mono inter_subset_left)

instance varietyMetricMeasure_isOpenPos (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Measure.IsOpenPosMeasure (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) :=
  ⟨fun _ hS hne => (varietyMetricMeasure_open_pos V hS hne).ne'⟩

end

/-! Unweighted Euclidean measure on a compact chart piece is bounded by
a finite multiple of the actual global projective metric measure. -/

open _root_.MeasureTheory Set
open scoped ENNReal

def varietyCompactChartPoint (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (K : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) (z : K) : V.analyticSpace :=
  e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z.val)

theorem varietyCompactChartPoint_continuous (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    {K : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hKU : K ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    Continuous (varietyCompactChartPoint V e K) :=
  e.continuousOn_symm.comp_continuous
    ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).continuous.comp continuous_subtype_val) (fun z => hKU z.property)

def varietyUnweightedChartMeasure (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (K : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :
    Measure V.analyticSpace :=
  Measure.map (varietyCompactChartPoint V e K)
    ((volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)).comap (Subtype.val : K → EuclideanMetric.CM.Construction.varietyEuclideanModel V))

theorem varietyUnweightedChartMeasure_apply (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    {K : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hK : MeasurableSet K) (hKU : K ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    {S : Set V.analyticSpace} (hS : MeasurableSet S) :
    varietyUnweightedChartMeasure V e K S = volume (K ∩ MetricChartMeasure.CM.Construction.varietyMetricChartCoordinates V e S) := by
  have hφ := (varietyCompactChartPoint_continuous V e hKU).measurable
  rw [varietyUnweightedChartMeasure, Measure.map_apply hφ hS,
    Measure.comap_apply _ Subtype.val_injective
      (fun s hs => (MeasurableEmbedding.subtype_coe hK).measurableSet_image.mpr hs) _ (hφ hS)]
  congr 1
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.property, (MetricChartMeasure.CM.Construction.mem_varietyMetricChartCoordinates V e S w.val).mpr ⟨hKU w.property, hw⟩⟩
  · intro hz
    exact ⟨⟨z, hz.1⟩, ((MetricChartMeasure.CM.Construction.mem_varietyMetricChartCoordinates V e S z).mp hz.2).2, rfl⟩

theorem varietyUnweightedChartMeasure_le (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {K : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hK : IsCompact K) (hKU : K ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ∃ B : ℝ≥0∞, B ≠ ∞ ∧ varietyUnweightedChartMeasure V e K ≤ B • GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V := by
  obtain ⟨c, hc, hρ⟩ := hK.exists_forall_le'
    ((Metric.CM.Construction.varietyMetricDensity_smooth V e he).continuousOn.mono hKU)
    (fun z hz => Metric.CM.Construction.varietyMetricDensity_pos V e he (hKU hz))
  have hc0 : ENNReal.ofReal c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hc)
  refine ⟨(ENNReal.ofReal c)⁻¹, ENNReal.inv_ne_top.mpr hc0, ?_⟩
  apply Measure.le_iff.mpr
  intro S hS
  rw [Measure.smul_apply, smul_eq_mul]
  apply (ENNReal.mul_le_iff_le_inv hc0 ENNReal.ofReal_ne_top).mp
  rw [varietyUnweightedChartMeasure_apply V e hK.measurableSet hKU hS]
  calc
    ENNReal.ofReal c * volume (K ∩ MetricChartMeasure.CM.Construction.varietyMetricChartCoordinates V e S) =
        ∫⁻ z in K ∩ MetricChartMeasure.CM.Construction.varietyMetricChartCoordinates V e S, ENNReal.ofReal c := by
      rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, mul_comm]
    _ ≤ ∫⁻ z in K ∩ MetricChartMeasure.CM.Construction.varietyMetricChartCoordinates V e S, ENNReal.ofReal (Metric.CM.Construction.varietyMetricDensity V e z) := by
      apply setLIntegral_mono' (hK.measurableSet.inter (MetricChartMeasure.CM.Construction.varietyMetricChartCoordinates_measurable V e hS))
      intro z hz
      exact ENNReal.ofReal_le_ofReal (hρ z hz.1)
    _ ≤ ∫⁻ z in MetricChartMeasure.CM.Construction.varietyMetricChartCoordinates V e S, ENNReal.ofReal (Metric.CM.Construction.varietyMetricDensity V e z) :=
      lintegral_mono_set inter_subset_right
    _ = MetricChartMeasure.CM.Construction.varietyMetricChartMeasure V e S := (MetricChartMeasure.CM.Construction.varietyMetricChartMeasure_apply V e hS).symm
    _ = (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V).restrict e.source S := by rw [GlobalMetricMeasure.CM.Construction.varietyMetricMeasure_restrict_chart V e he]
    _ ≤ GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V S := Measure.restrict_apply_le _ _

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartMeasure.CM.Construction

import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartMeasure

/-! # Chart Almost Everywhere -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction

noncomputable section

section

/-! The metric measure on a compact chart image is bounded above by its
unweighted Euclidean pushforward, allowing bounded reconstruction in L2. -/

open _root_.MeasureTheory Set
open scoped ENNReal

def varietyCompactChartImage (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (K : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :
    Set V.analyticSpace := (fun z => e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) '' K

theorem varietyCompactChartImage_isCompact (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    {K : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hK : IsCompact K) (hKU : K ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    IsCompact (varietyCompactChartImage V e K) :=
  hK.image_of_continuousOn
    (e.continuousOn_symm.comp (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).continuous.continuousOn hKU)

theorem varietyCompactChartImage_subset_source (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    {K : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hKU : K ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    varietyCompactChartImage V e K ⊆ e.source := by
  rintro x ⟨z, hz, rfl⟩
  exact e.map_target (hKU hz)

theorem varietyChartPoint_injOn (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) :
    InjOn (fun z => e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) := by
  intro z hz w hw hzw
  apply (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).injective
  have h := congrArg e hzw
  rwa [e.right_inv hz, e.right_inv hw] at h

theorem varietyMetricChartCoordinates_image_inter (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    {K : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hKU : K ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (S : Set V.analyticSpace) :
    MetricChartMeasure.CM.Construction.varietyMetricChartCoordinates V e (varietyCompactChartImage V e K ∩ S) =
      K ∩ MetricChartMeasure.CM.Construction.varietyMetricChartCoordinates V e S := by
  ext z
  simp only [MetricChartMeasure.CM.Construction.mem_varietyMetricChartCoordinates, mem_inter_iff]
  constructor
  · rintro ⟨hz, ⟨⟨w, hw, heq⟩, hS⟩⟩
    have hzw := varietyChartPoint_injOn V e (hKU hw) hz heq
    exact ⟨hzw ▸ hw, hz, hS⟩
  · rintro ⟨hzK, hzU, hzS⟩
    exact ⟨hzU, ⟨z, hzK, rfl⟩, hzS⟩

theorem varietyMetricMeasure_restrict_image_apply (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {K : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hK : IsCompact K) (hKU : K ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    {S : Set V.analyticSpace} (hS : MeasurableSet S) :
    (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V).restrict (varietyCompactChartImage V e K) S =
      ∫⁻ z in K ∩ MetricChartMeasure.CM.Construction.varietyMetricChartCoordinates V e S, ENNReal.ofReal (Metric.CM.Construction.varietyMetricDensity V e z) := by
  have hIm := (varietyCompactChartImage_isCompact V e hK hKU).measurableSet
  rw [Measure.restrict_apply hS, inter_comm S,
    ← Measure.restrict_eq_self (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V)
      (inter_subset_left.trans (varietyCompactChartImage_subset_source V e hKU)),
    GlobalMetricMeasure.CM.Construction.varietyMetricMeasure_restrict_chart V e he,
    MetricChartMeasure.CM.Construction.varietyMetricChartMeasure_apply V e (hIm.inter hS), varietyMetricChartCoordinates_image_inter V e hKU]

theorem varietyMetricMeasure_restrict_image_le (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {K : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hK : IsCompact K) (hKU : K ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ∃ B : ℝ≥0∞, B ≠ ∞ ∧ (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V).restrict (varietyCompactChartImage V e K) ≤
      B • ChartMeasure.CM.Construction.varietyUnweightedChartMeasure V e K := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    ((Metric.CM.Construction.varietyMetricDensity_smooth V e he).continuousOn.mono hKU)
  refine ⟨ENNReal.ofReal B, ENNReal.ofReal_ne_top, Measure.le_iff.mpr (fun S hS => ?_)⟩
  rw [varietyMetricMeasure_restrict_image_apply V e he hK hKU hS, Measure.smul_apply, smul_eq_mul,
    ChartMeasure.CM.Construction.varietyUnweightedChartMeasure_apply V e hK.measurableSet hKU hS]
  calc
    _ ≤ ∫⁻ z in K ∩ MetricChartMeasure.CM.Construction.varietyMetricChartCoordinates V e S, ENNReal.ofReal B := by
      apply setLIntegral_mono' (hK.measurableSet.inter (MetricChartMeasure.CM.Construction.varietyMetricChartCoordinates_measurable V e hS))
      intro z hz
      exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hB z hz.1))
    _ = _ := by rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, mul_comm]

theorem varietyCompactChartPoint_measurableEmbedding (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    {K : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hK : IsCompact K) (hKU : K ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    MeasurableEmbedding (ChartMeasure.CM.Construction.varietyCompactChartPoint V e K) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  apply ((ChartMeasure.CM.Construction.varietyCompactChartPoint_continuous V e hKU).isClosedEmbedding ?_).measurableEmbedding
  intro z w h
  apply Subtype.ext
  exact varietyChartPoint_injOn V e (hKU z.property) (hKU w.property) h

end

/-! Euclidean almost-everywhere identities on compact chart pieces
transport to the actual global metric measure on their chart images. -/

open _root_.MeasureTheory Set Filter

theorem varietyChartImage_ae_of_ae (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {K : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hK : IsCompact K) (hKU : K ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    {P : EuclideanMetric.CM.Construction.varietyEuclideanModel V → Prop} (hP : ∀ᵐ z ∂(volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)), P z) :
    ∀ᵐ x ∂(GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V).restrict (varietyCompactChartImage V e K),
      P ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x)) := by
  let ν := (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)).comap (Subtype.val : K → EuclideanMetric.CM.Construction.varietyEuclideanModel V)
  let φ := ChartMeasure.CM.Construction.varietyCompactChartPoint V e K
  have hφ := varietyCompactChartPoint_measurableEmbedding V e hK hKU
  have hpK : ∀ᵐ z ∂ν, P z.val :=
    (ae_restrict_iff_subtype hK.measurableSet).mp (ae_restrict_of_ae hP)
  have hpX : ∀ᵐ x ∂ ChartMeasure.CM.Construction.varietyUnweightedChartMeasure V e K,
      P ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x)) := by
    apply hφ.ae_map_iff.mpr
    filter_upwards [hpK] with z hz
    change P ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z.val))))
    rw [e.right_inv (hKU z.property), ContinuousLinearEquiv.symm_apply_apply]
    exact hz
  have hac : (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V).restrict (varietyCompactChartImage V e K) ≪
      ChartMeasure.CM.Construction.varietyUnweightedChartMeasure V e K :=
    Measure.absolutelyContinuous_of_le_smul (varietyMetricMeasure_restrict_image_le V e he hK hKU).choose_spec.2
  exact hac.ae_le hpX

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction

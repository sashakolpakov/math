import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormChartLocalization
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.FrameIdentity
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.FiniteMetricCutoffs

/-! # One Form Localization Faithful -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormLocalizationFaithful.CM.Construction

noncomputable section

/-! The finite family of actual chart-localized covector fields detects
zero in the global metric L2 space. -/

open _root_.MeasureTheory Set Filter

theorem varietyOneFormChartL2_detects_zero (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V) (G : FiniteMetricCutoffs.CM.Construction.CompactMetricCutoffs V C)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (u : Lp (EuclideanSpace ℂ ι) 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V))
    (hu : ∀ i, OneFormChartLocalization.CM.Construction.varietyOneFormChartL2 V C b (C.chart i) (C.chart_mem i)
      (G.cutoff i) (G.compact_support i) (G.supported i) u = 0) : u = 0 := by
  have hpiece (i : Fin C.size) : ∀ᵐ x ∂ GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V, x ∈ C.piece i → u x = 0 := by
    let e := C.chart i
    let g := G.cutoff i
    let K := ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage V e (tsupport g)
    have hflat : ∀ᵐ z ∂(volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)),
        g z • ChartFrameLp.CM.Construction.varietyChartFrameCoefficient V C b e K (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))
          (u (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))) = 0 := by
      have h := OneFormChartLocalization.CM.Construction.varietyOneFormChartL2_coe V C b e (C.chart_mem i) g (G.compact_support i) (G.supported i) u
      rw [hu i] at h
      filter_upwards [h, Lp.coeFn_zero (EuclideanSpace ℂ ι) 2 (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V))] with z hz hzero
      exact hz.symm.trans hzero
    have himage := ChartAlmostEverywhere.CM.Construction.varietyChartImage_ae_of_ae V e (C.chart_mem i) (G.compact_support i) (G.supported i) hflat
    have hK : MeasurableSet K := (ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_isCompact V e (G.compact_support i) (G.supported i)).measurableSet
    filter_upwards [(ae_restrict_iff' hK).mp himage] with x hx hxi
    have hex : x ∈ e.source := C.piece_subset_source i hxi
    have hg1 : g ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x)) = 1 := G.one_on_compact i x (C.piece_subset i hxi)
    have hz : (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x) ∈ tsupport g := by
      apply subset_tsupport g
      change g ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x)) ≠ 0
      rw [hg1]
      exact one_ne_zero
    have hxK : x ∈ K := ⟨(EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x), hz, by
      dsimp only
      rw [ContinuousLinearEquiv.apply_symm_apply, e.left_inv hex]⟩
    have hx' := hx hxK
    rw [hg1, one_smul, ContinuousLinearEquiv.apply_symm_apply, e.left_inv hex] at hx'
    rw [FrameIdentity.CM.Construction.varietyChartFrameCoefficient_on_own_piece V C b i hxK hxi, ContinuousLinearMap.id_apply] at hx'
    exact hx'
  have hall : ∀ᵐ x ∂ GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V, ∀ i, x ∈ C.piece i → u x = 0 := ae_all_iff.mpr hpiece
  apply Lp.ext
  filter_upwards [hall, Lp.coeFn_zero (EuclideanSpace ℂ ι) 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V)] with x hx hz
  obtain ⟨i, hi⟩ := C.exists_piece x
  exact (hx i hi).trans hz.symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormLocalizationFaithful.CM.Construction

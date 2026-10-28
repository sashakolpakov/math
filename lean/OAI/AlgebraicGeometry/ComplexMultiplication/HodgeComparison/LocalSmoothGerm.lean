import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalLocalRepresentative
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere

/-! # Local Smooth Germ -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LocalSmoothGerm.CM.Construction

noncomputable section

/-! A smooth chart representative gives an actual global smooth zero-form
which agrees with the L2 function on a neighborhood of the chosen point. -/

open _root_.MeasureTheory Set Filter
open scoped SchwartzMap ContDiff _root_.Topology

theorem varietyChartImage_isOpen (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    {W : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hW : IsOpen W) (hWU : W ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    IsOpen (ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage V e W) := by
  have hL : IsOpen (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V '' W) :=
    (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).toHomeomorph.isOpenMap W hW
  have hLt : EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V '' W ⊆ e.target := by
    rintro y ⟨w, hw, rfl⟩
    exact hWU hw
  simpa only [ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage, image_image] using e.isOpen_image_symm_of_subset_target hL hLt

theorem chart_smooth_representative_global_germ (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (u : Lp ℂ 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V))
    {U : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hU : IsOpen U) (hUe : U ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ U)
    (v : BoundedContinuousFunction (EuclideanMetric.CM.Construction.varietyEuclideanModel V) ℂ)
    (hvs : ContDiff ℝ (⊤ : ℕ∞) (v : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hrep : ∀ᵐ y ∂(volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)), y ∈ U →
      v y = u (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V y))) :
    ∃ N : Set V.analyticSpace, IsOpen N ∧ e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) ∈ N ∧
      ∃ f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0,
        u =ᵐ[(GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V).restrict N] HolomorphicPrimitive.CM.Construction.zeroFormScalar f := by
  obtain ⟨δ, hδc, hδU, _hδreal, hδz⟩ := NestedCutoffExistence.CM.Construction.exists_real_schwartz_cutoff_near_compact
    (isCompact_singleton (x := z)) hU (singleton_subset_iff.mpr hz)
  have hδe := hδU.trans hUe
  let g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ) :=
    (hδc.mul_right (f' := (v : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))).toSchwartzMap ((δ.smooth ⊤).mul hvs)
  have hgK : tsupport g ⊆ tsupport δ := by
    apply closure_minimal ?_ (isClosed_tsupport _)
    intro y hy
    apply subset_tsupport δ
    intro hδy
    apply hy
    change δ y * v y = 0
    rw [hδy, zero_mul]
  have hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ) :=
    hδc.of_isClosed_subset (isClosed_tsupport _) hgK
  let f := ChartTestFunction.CM.Construction.varietyChartTestForm V e he g hgc (hgK.trans hδe)
  have hW : {y | δ y = 1} ∩ U ∈ 𝓝 z :=
    inter_mem (hδz z (mem_singleton z)) (hU.mem_nhds hz)
  obtain ⟨W, hWW, hWo, hzW⟩ := mem_nhds_iff.mp hW
  have hWK : W ⊆ tsupport δ := by
    intro y hy
    apply subset_tsupport δ
    change δ y ≠ 0
    rw [(hWW hy).1]
    exact one_ne_zero
  have hWe : W ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := hWK.trans hδe
  let N := ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage V e W
  have hNo : IsOpen N := varietyChartImage_isOpen V e hWo hWe
  have hrepK := ChartAlmostEverywhere.CM.Construction.varietyChartImage_ae_of_ae V e he hδc hδe hrep
  have hKmeas := (ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_isCompact V e hδc hδe).measurableSet
  have hrepK' := (ae_restrict_iff' hKmeas).mp hrepK
  refine ⟨N, hNo, ⟨z, hzW, rfl⟩, f, (ae_restrict_iff' hNo.measurableSet).mpr ?_⟩
  filter_upwards [hrepK'] with x hx
  rintro ⟨y, hy, rfl⟩
  have h := hx (show e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V y) ∈ ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage V e (tsupport δ) from
    ⟨y, hWK hy, rfl⟩)
  rw [e.right_inv (hWe hy), ContinuousLinearEquiv.symm_apply_apply] at h
  have hval := ChartTestFunction.CM.Construction.varietyChartTestForm_in_chart V e he g hgc (hgK.trans hδe) (hWe hy)
  change HolomorphicPrimitive.CM.Construction.zeroFormScalar f (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V y)) = δ y * v y at hval
  rw [(hWW hy).1, one_mul] at hval
  exact (h ((hWW hy).2)).symm.trans hval.symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LocalSmoothGerm.CM.Construction

import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartFrameLp

/-! # One Form Chart Localization -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormChartLocalization.CM.Construction

noncomputable section

/-! Bounded localization of actual global L2 covector fields into
Euclidean chart components, agreeing with smooth form coordinates. -/

open _root_.MeasureTheory Set Filter
open scoped SchwartzMap

variable {ι : Type*} [Fintype ι]

def varietyOneFormChartL2 (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    Lp (EuclideanSpace ℂ ι) 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) →L[ℝ]
      Lp (EuclideanSpace ℂ ι) 2 (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :=
  (ChartCutoffLp.CM.Construction.varietyChartCutoffL2 V e he g hgc hg).comp
    (ChartFrameLp.CM.Construction.varietyChartFrameL2 V C b e he (ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_isCompact V e hgc hg)
      (ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_subset_source V e hg))

theorem varietyOneFormChartL2_coe (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (u : Lp (EuclideanSpace ℂ ι) 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V)) :
    varietyOneFormChartL2 V C b e he g hgc hg u =ᵐ[volume] fun z =>
      g z • ChartFrameLp.CM.Construction.varietyChartFrameCoefficient V C b e (ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage V e (tsupport g))
        (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) (u (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))) := by
  let hK := ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_isCompact V e hgc hg
  let hKe := ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_subset_source V e hg
  have hm := ChartFrameLp.CM.Construction.varietyChartFrameL2_coe V C b e he hK hKe u
  exact ChartCutoffLp.CM.Construction.varietyChartCutoffL2_coe_of_ae (F := EuclideanSpace ℂ ι) V e he g hgc hg
    (ChartFrameLp.CM.Construction.varietyChartFrameL2 V C b e he hK hKe u)
    (fun x => ChartFrameLp.CM.Construction.varietyChartFrameCoefficient V C b e (ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage V e (tsupport g)) x (u x)) hm

theorem varietyOneFormChartL2_form (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) :
    varietyOneFormChartL2 V C b e he g hgc hg (GlobalLp.CM.Construction.varietyOneFormL2 V C b form) =ᵐ[volume]
      fun z => g z • GlobalLp.CM.Construction.varietyOneFormInChart V b e form (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) := by
  let K := ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage V e (tsupport g)
  let hK := ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_isCompact V e hgc hg
  let hKe := ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_subset_source V e hg
  have hm : ChartFrameLp.CM.Construction.varietyChartFrameL2 V C b e he hK hKe (GlobalLp.CM.Construction.varietyOneFormL2 V C b form) =ᵐ[GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V]
      fun x => ChartFrameLp.CM.Construction.varietyChartFrameCoefficient V C b e K x (GlobalLp.CM.Construction.varietyOneFormField V C b form x) := by
    filter_upwards [ChartFrameLp.CM.Construction.varietyChartFrameL2_coe V C b e he hK hKe (GlobalLp.CM.Construction.varietyOneFormL2 V C b form),
      GlobalLp.CM.Construction.varietyOneFormL2_coe V C b form] with x hx hf
    rw [hx, hf]
  have h := ChartCutoffLp.CM.Construction.varietyChartCutoffL2_coe_of_ae V e he g hgc hg _ _ hm
  filter_upwards [h] with z hz
  change ChartCutoffLp.CM.Construction.varietyChartCutoffL2 V e he g hgc hg
    (ChartFrameLp.CM.Construction.varietyChartFrameL2 V C b e he hK hKe (GlobalLp.CM.Construction.varietyOneFormL2 V C b form)) z = _
  rw [hz]
  by_cases hzg : z ∈ tsupport g
  · rw [ChartFrameLp.CM.Construction.varietyChartFrameCoefficient_form V C b e he hKe form (show e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) ∈ K from ⟨z, hzg, rfl⟩)]
  · rw [image_eq_zero_of_notMem_tsupport hzg, zero_smul, zero_smul]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormChartLocalization.CM.Construction

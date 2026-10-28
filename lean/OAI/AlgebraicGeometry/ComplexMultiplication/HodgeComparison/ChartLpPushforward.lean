import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpEmbeddingExtension
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpRestrictedExtension

/-! # Chart Lp Pushforward -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartLpPushforward.CM.Construction

noncomputable section

/-! Bounded reconstruction of a global metric L2 function from a compact
Euclidean chart piece, with its actual coordinate and support formula. -/

open _root_.MeasureTheory Set Filter

def varietyChartL2Pushforward (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {K : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hK : IsCompact K) (hKU : K ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    Lp ℂ 2 (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) →L[ℝ] Lp ℂ 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) := by
  let ν : Measure K := (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)).comap
    (Subtype.val : K → EuclideanMetric.CM.Construction.varietyEuclideanModel V)
  let φ : K → V.analyticSpace := ChartMeasure.CM.Construction.varietyCompactChartPoint V e K
  let P : Lp ℂ 2 (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) →L[ℝ] Lp ℂ 2 ν :=
    (LpLocalization.CM.Construction.lpSubtypeRestriction (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) hK.measurableSet).restrictScalars ℝ
  let E : Lp ℂ 2 ν →L[ℝ] Lp ℂ 2 (ChartMeasure.CM.Construction.varietyUnweightedChartMeasure V e K) :=
    (LpEmbeddingExtension.CM.Construction.lpMeasurableEmbeddingExtension (𝕜 := ℝ) ν φ (ChartAlmostEverywhere.CM.Construction.varietyCompactChartPoint_measurableEmbedding V e hK hKU)).toContinuousLinearMap
  let hB := (ChartAlmostEverywhere.CM.Construction.varietyMetricMeasure_restrict_image_le V e he hK hKU).choose_spec
  let Q : Lp ℂ 2 (ChartMeasure.CM.Construction.varietyUnweightedChartMeasure V e K) →L[ℝ]
      Lp ℂ 2 ((GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V).restrict (ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage V e K)) :=
    Lp.LpToLpOfMeasureLeSMul hB.1 hB.2
  let Z : Lp ℂ 2 ((GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V).restrict (ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage V e K)) →L[ℝ]
      Lp ℂ 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) :=
    (LpRestrictedExtension.CM.Construction.lpRestrictedZeroExtension (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V)
      (ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_isCompact V e hK hKU).measurableSet).toContinuousLinearMap.restrictScalars ℝ
  exact Z.comp (Q.comp (E.comp P))

theorem varietyChartL2Pushforward_coe_of_ae (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {K : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hK : IsCompact K) (hKU : K ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (u : Lp ℂ 2 (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V))) (f : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ)
    (hf : u =ᵐ[volume] f) :
    varietyChartL2Pushforward V e he hK hKU u =ᵐ[GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V]
      (ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage V e K).indicator (fun x => f ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x))) := by
  let ν := (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)).comap (Subtype.val : K → EuclideanMetric.CM.Construction.varietyEuclideanModel V)
  let φ := ChartMeasure.CM.Construction.varietyCompactChartPoint V e K
  let hφ := ChartAlmostEverywhere.CM.Construction.varietyCompactChartPoint_measurableEmbedding V e hK hKU
  let P := LpLocalization.CM.Construction.lpSubtypeRestriction (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) hK.measurableSet u
  let E := LpEmbeddingExtension.CM.Construction.lpMeasurableEmbeddingExtension (𝕜 := ℝ) ν φ hφ P
  let hB := (ChartAlmostEverywhere.CM.Construction.varietyMetricMeasure_restrict_image_le V e he hK hKU).choose_spec
  let Q : Lp ℂ 2 ((GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V).restrict (ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage V e K)) :=
    Lp.LpToLpOfMeasureLeSMul hB.1 hB.2 E
  have hP : P =ᵐ[ν] (fun z : K => f z.val) :=
    (LpLocalization.CM.Construction.lpSubtypeRestriction_coeFn (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) hK.measurableSet u).trans
      ((ae_restrict_iff_subtype hK.measurableSet).mp (ae_restrict_of_ae hf))
  have hE : E =ᵐ[ChartMeasure.CM.Construction.varietyUnweightedChartMeasure V e K]
      LpEmbeddingExtension.CM.Construction.measurableEmbeddingExtension φ (fun z : K => f z.val) :=
    (LpEmbeddingExtension.CM.Construction.lpMeasurableEmbeddingExtension_coe (𝕜 := ℝ) ν φ hφ P).trans (LpEmbeddingExtension.CM.Construction.measurableEmbeddingExtension_ae ν φ hφ hP)
  have hac : (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V).restrict (ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage V e K) ≪
      ChartMeasure.CM.Construction.varietyUnweightedChartMeasure V e K := Measure.absolutelyContinuous_of_le_smul hB.2
  have hQ : Q =ᵐ[(GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V).restrict (ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage V e K)]
      LpEmbeddingExtension.CM.Construction.measurableEmbeddingExtension φ (fun z : K => f z.val) :=
    (Lp.coeFn_LpToLpOfMeasureLeSMul hB.1 hB.2 E).trans (hac.ae_eq hE)
  have hQf : Q =ᵐ[(GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V).restrict (ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage V e K)]
      (fun x => f ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x))) := by
    filter_upwards [hQ, ae_restrict_mem (ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_isCompact V e hK hKU).measurableSet] with x hx hxK
    rw [hx]
    obtain ⟨z, hz, rfl⟩ := hxK
    change Function.extend φ (fun z : K => f z.val) 0 (φ ⟨z, hz⟩) = _
    rw [hφ.injective.extend_apply]
    change f z = f ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))))
    rw [e.right_inv (hKU hz), ContinuousLinearEquiv.symm_apply_apply]
  exact LpRestrictedExtension.CM.Construction.lpRestrictedZeroExtension_coe_of_ae (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V)
    (ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_isCompact V e hK hKU).measurableSet Q _ hQf

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartLpPushforward.CM.Construction

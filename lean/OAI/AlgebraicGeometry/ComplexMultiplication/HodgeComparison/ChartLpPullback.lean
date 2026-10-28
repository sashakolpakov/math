import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartMeasure
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpLocalization

/-! # Chart Lp Pullback -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartLpPullback.CM.Construction

noncomputable section

/-! Bounded restriction of global metric L2 functions to actual compact
Euclidean chart pieces, with an almost-everywhere coordinate formula. -/

open _root_.MeasureTheory Set Filter

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def varietyCompactChartPullback (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {K : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hK : IsCompact K) (hKU : K ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    Lp F 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) →L[ℝ]
      Lp F 2 ((volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)).comap (Subtype.val : K → EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (ChartMeasure.CM.Construction.varietyCompactChartPoint V e K)
    ⟨(ChartMeasure.CM.Construction.varietyCompactChartPoint_continuous V e hKU).measurable, rfl⟩).toContinuousLinearMap.comp
      (Lp.LpToLpOfMeasureLeSMul (ChartMeasure.CM.Construction.varietyUnweightedChartMeasure_le V e he hK hKU).choose_spec.1
        (ChartMeasure.CM.Construction.varietyUnweightedChartMeasure_le V e he hK hKU).choose_spec.2)

theorem varietyCompactChartPullback_coe (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {K : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hK : IsCompact K) (hKU : K ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (u : Lp F 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V)) :
    varietyCompactChartPullback V e he hK hKU u =ᵐ[
        (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)).comap (Subtype.val : K → EuclideanMetric.CM.Construction.varietyEuclideanModel V)]
      u ∘ ChartMeasure.CM.Construction.varietyCompactChartPoint V e K := by
  let ν := (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)).comap (Subtype.val : K → EuclideanMetric.CM.Construction.varietyEuclideanModel V)
  have hφ : MeasurePreserving (ChartMeasure.CM.Construction.varietyCompactChartPoint V e K) ν (ChartMeasure.CM.Construction.varietyUnweightedChartMeasure V e K) :=
    ⟨(ChartMeasure.CM.Construction.varietyCompactChartPoint_continuous V e hKU).measurable, rfl⟩
  let h := (ChartMeasure.CM.Construction.varietyUnweightedChartMeasure_le V e he hK hKU).choose_spec
  let T : Lp F 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) →L[ℝ] Lp F 2 (ChartMeasure.CM.Construction.varietyUnweightedChartMeasure V e K) :=
    Lp.LpToLpOfMeasureLeSMul h.1 h.2
  exact (Lp.coeFn_compMeasurePreserving (T u) hφ).trans
    (hφ.quasiMeasurePreserving.ae (Lp.coeFn_LpToLpOfMeasureLeSMul h.1 h.2 u))

theorem varietyCompactChartPoint_ae (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {K : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hK : IsCompact K) (hKU : K ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    {P : V.analyticSpace → Prop} (hP : ∀ᵐ x ∂ GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V, P x) :
    ∀ᵐ z ∂(volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)).comap (Subtype.val : K → EuclideanMetric.CM.Construction.varietyEuclideanModel V),
      P (ChartMeasure.CM.Construction.varietyCompactChartPoint V e K z) := by
  have hφ : MeasurePreserving (ChartMeasure.CM.Construction.varietyCompactChartPoint V e K)
      ((volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)).comap (Subtype.val : K → EuclideanMetric.CM.Construction.varietyEuclideanModel V))
      (ChartMeasure.CM.Construction.varietyUnweightedChartMeasure V e K) :=
    ⟨(ChartMeasure.CM.Construction.varietyCompactChartPoint_continuous V e hKU).measurable, rfl⟩
  have hac : ChartMeasure.CM.Construction.varietyUnweightedChartMeasure V e K ≪ GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V :=
    Measure.absolutelyContinuous_of_le_smul (ChartMeasure.CM.Construction.varietyUnweightedChartMeasure_le V e he hK hKU).choose_spec.2
  exact hφ.quasiMeasurePreserving.ae (hac.ae_le hP)

variable [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

def varietyChartL2Localization (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {K : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hK : IsCompact K) (hKU : K ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    Lp F 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) →L[ℝ] Lp F 2 (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :=
  ((LpLocalization.CM.Construction.lpSubtypeZeroExtension (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) hK.measurableSet).toContinuousLinearMap.restrictScalars ℝ).comp
    (varietyCompactChartPullback V e he hK hKU)

theorem varietyChartL2Localization_coe_of_ae (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {K : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hK : IsCompact K) (hKU : K ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (u : Lp F 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V)) (f : V.analyticSpace → F)
    (hf : u =ᵐ[GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V] f) :
    varietyChartL2Localization V e he hK hKU u =ᵐ[volume]
      K.indicator (fun z => f (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))) := by
  have hsub : varietyCompactChartPullback V e he hK hKU u =ᵐ[
        (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)).comap (Subtype.val : K → EuclideanMetric.CM.Construction.varietyEuclideanModel V)]
      f ∘ ChartMeasure.CM.Construction.varietyCompactChartPoint V e K :=
    (varietyCompactChartPullback_coe V e he hK hKU u).trans
      (varietyCompactChartPoint_ae V e he hK hKU hf)
  have hext := LpLocalization.CM.Construction.subtypeZeroExtension_ae_eq (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) hK.measurableSet hsub
  refine (LpLocalization.CM.Construction.subtypeZeroExtension_memLp (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) hK.measurableSet
    (varietyCompactChartPullback V e he hK hKU u)).coeFn_toLp.trans (hext.trans ?_)
  apply Eventually.of_forall
  intro z
  by_cases hz : z ∈ K
  · rw [LpLocalization.CM.Construction.subtypeZeroExtension_apply_mem _ hz, indicator_of_mem hz]
    rfl
  · rw [LpLocalization.CM.Construction.subtypeZeroExtension_apply_notMem _ hz, indicator_of_notMem hz]

theorem varietyChartL2Localization_coe (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {K : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hK : IsCompact K) (hKU : K ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (u : Lp F 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V)) :
    varietyChartL2Localization V e he hK hKU u =ᵐ[volume]
      K.indicator (fun z => u (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))) :=
  varietyChartL2Localization_coe_of_ae V e he hK hKU u u Filter.EventuallyEq.rfl

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartLpPullback.CM.Construction

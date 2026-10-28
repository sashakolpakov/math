import OAI.AlgebraicGeometry.DivisorClass.Chern.RealChartExtension
import OAI.Analysis.HodgeTheory.Decomposition.ChartIntegral

/-! # Global Pair Chart Integral -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The native coordinate bundle metric integral equals its original global metric-volume integral with the actual extended chart function. -/

open _root_.MeasureTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.Analysis.HodgeTheory.Decomposition.ChartIntegral.Constructions

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveGlobalPair_chart_integral (n : ℕ)
    (a c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) (f : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hs : tsupport f ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    (∫ z, h.projectiveGlobalPair V e n a c z * (f z : ℂ)) =
      ∫ x, h.globalFormPair V n a c x * (RealChartExtension.projectiveRealChartExtension V e f x : ℂ) ∂ Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.projectiveMetricVolume V := by
  let Φ := fun x => h.globalFormPair V n a c x * (RealChartExtension.projectiveRealChartExtension V e f x : ℂ)
  have hΦ : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ Φ :=
    (contDiff_mul : ContDiff ℝ ∞ (fun p : ℂ × ℂ => p.1 * p.2)).contMDiff.comp
      ((h.globalFormPair_smooth V n a c).prodMk_space
        (Complex.ofRealCLM.contDiff.contMDiff.comp (RealChartExtension.projectiveRealChartExtension_smooth V e he f hf hc hs)))
  have hzΦ (x : V.analyticSpace) (hx : x ∉ e.source) : Φ x = 0 := by
    dsimp only [Φ]
    rw [RealChartExtension.projectiveRealChartExtension_zero V e f hx, Complex.ofReal_zero, mul_zero]
  have hchart := Analysis.HodgeTheory.Decomposition.ChartIntegral.Constructions.projectiveMetricVolume_integral_chart V e he Φ hΦ.continuous.aestronglyMeasurable hzΦ
  calc
    _ = ∫ z in ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e, h.projectiveGlobalPair V e n a c z * (f z : ℂ) := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      rw [image_eq_zero_of_notMem_tsupport (fun ht => hz (hs ht)), Complex.ofReal_zero, mul_zero]
    _ = ∫ z in ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e, ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z • Φ (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) := by
      apply setIntegral_congr_fun (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.measurableSet
      intro z hz
      dsimp only [Φ, HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveGlobalPair]
      rw [RealChartExtension.projectiveRealChartExtension_inverse V e f hz, Complex.real_smul]
      ring
    _ = _ := hchart.symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern

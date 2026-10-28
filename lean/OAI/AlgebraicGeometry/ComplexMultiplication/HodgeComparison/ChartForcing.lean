import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartTestFunction
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricBochnerIntegration

/-! # Chart Forcing -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartForcing.CM.Construction

noncomputable section

/-! Smooth global forcing gives a genuine compact Schwartz forcing in a
metric chart, and the corresponding test pairings agree exactly. -/

open _root_.MeasureTheory Set Filter
open scoped SchwartzMap ContDiff _root_.Topology

theorem varietyChartForcing_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (χ : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hχU : tsupport χ ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (F : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0) :
    ContDiff ℝ ∞ (fun z => χ z * (Metric.CM.Construction.varietyMetricDensity V e z • ScalarChartLocalization.CM.Construction.varietyScalarChart V e F z)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e
  · exact (χ.smooth ⊤).contDiffAt.mul
      (((Metric.CM.Construction.varietyMetricDensity_smooth V e he).contDiffAt ((EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)).smul
        ((ScalarChartLocalization.CM.Construction.varietyScalarChart_smooth V e he F).contDiffAt ((EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)))
  · have hzero : (χ : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ) =ᶠ[𝓝 z] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp (fun h => hz (hχU h))
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [hzero] with y hy
    simp only [hy, Pi.zero_apply, zero_mul]

def varietyChartForcing (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (χ : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hχc : HasCompactSupport (χ : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hχU : tsupport χ ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (F : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0) : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ) :=
  (hχc.mul_right (f' := fun z => Metric.CM.Construction.varietyMetricDensity V e z • ScalarChartLocalization.CM.Construction.varietyScalarChart V e F z)).toSchwartzMap
    (varietyChartForcing_smooth V e he χ hχU F)

theorem varietyChartForcing_apply (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (χ : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hχc : HasCompactSupport (χ : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hχU : tsupport χ ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (F : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0) (z : EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    varietyChartForcing V e he χ hχc hχU F z = χ z * (Metric.CM.Construction.varietyMetricDensity V e z • ScalarChartLocalization.CM.Construction.varietyScalarChart V e F z) := rfl

theorem varietyChartForcing_pairing (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (F : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0)
    (g χ : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ))
    (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hgU : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (hχc : HasCompactSupport (χ : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hχU : tsupport χ ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (hχ : ∀ z ∈ tsupport g, χ z = 1) :
    inner ℝ (GlobalLp.CM.Construction.varietySmoothScalarL2 V F)
      (GlobalLp.CM.Construction.varietySmoothScalarL2 V (ChartTestFunction.CM.Construction.varietyChartTestForm V e he g hgc hgU)) =
    inner ℝ ((varietyChartForcing V e he χ hχc hχU F).toLp 2) (g.toLp 2) := by
  let T := ChartTestFunction.CM.Construction.varietyChartTestForm V e he g hgc hgU
  let f := fun x => inner ℝ (HolomorphicPrimitive.CM.Construction.zeroFormScalar F x) (HolomorphicPrimitive.CM.Construction.zeroFormScalar T x)
  have hm : AEStronglyMeasurable f (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) :=
    (innerSL ℝ).aestronglyMeasurable_comp₂
      (Intersection.CM.Construction.zeroFormScalar_continuous F).aestronglyMeasurable (Intersection.CM.Construction.zeroFormScalar_continuous T).aestronglyMeasurable
  have hzero : ∀ x, x ∉ e.source → f x = 0 := by
    intro x hx
    change inner ℝ (HolomorphicPrimitive.CM.Construction.zeroFormScalar F x) (ChartTestFunction.CM.Construction.varietyChartTestScalar V e g x) = 0
    rw [ChartTestFunction.CM.Construction.varietyChartTestScalar, indicator_of_notMem hx, inner_zero_right]
  calc
    _ = ∫ x, f x ∂ GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [GlobalLp.CM.Construction.varietySmoothScalarL2_coe V F, GlobalLp.CM.Construction.varietySmoothScalarL2_coe V T] with x hF hT
      change inner ℝ (GlobalLp.CM.Construction.varietySmoothScalarL2 V F x) (GlobalLp.CM.Construction.varietySmoothScalarL2 V T x) = f x
      rw [hF, hT]
    _ = ∫ x in e.source, f x ∂ GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    _ = ∫ z in (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)),
        Metric.CM.Construction.varietyMetricDensity V e z • f (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) :=
      MetricBochnerIntegration.CM.Construction.varietyMetricMeasure_integral_chart V e he f hm
    _ = ∫ z in (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)),
        inner ℝ (varietyChartForcing V e he χ hχc hχU F z) (g z) := by
      apply setIntegral_congr_fun (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.measurableSet
      intro z hz
      change Metric.CM.Construction.varietyMetricDensity V e z • inner ℝ (ScalarChartLocalization.CM.Construction.varietyScalarChart V e F z)
        (ScalarChartLocalization.CM.Construction.varietyScalarChart V e T z) = _
      dsimp only
      rw [ChartTestFunction.CM.Construction.varietyChartTestForm_in_chart V e he g hgc hgU hz, varietyChartForcing_apply]
      by_cases hzg : z ∈ tsupport g
      · rw [hχ z hzg, one_mul, real_inner_smul_left, smul_eq_mul]
      · rw [image_eq_zero_of_notMem_tsupport hzg, inner_zero_right, inner_zero_right, smul_zero]
    _ = ∫ z, inner ℝ (varietyChartForcing V e he χ hχc hχU F z) (g z) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
        rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hgU h)), inner_zero_right])
    _ = _ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(varietyChartForcing V e he χ hχc hχU F).coeFn_toLp 2, g.coeFn_toLp 2] with z hF hg
      rw [hF, hg]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartForcing.CM.Construction

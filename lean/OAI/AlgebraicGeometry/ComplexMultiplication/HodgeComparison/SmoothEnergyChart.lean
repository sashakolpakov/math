import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricEnergyInvariant
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricBochnerIntegration
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricNormalization
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartTestDifferential

/-! # Smooth Energy Chart -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothEnergyChart.CM.Construction

noncomputable section

/-! A global metric energy with a chart-supported smooth test form is
exactly the actual density-weighted Euclidean energy in that chart. -/

open Set _root_.MeasureTheory
open scoped SchwartzMap

variable {ι : Type*} [Fintype ι]

theorem varietySmoothEnergy_aestronglyMeasurable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V) (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (form other : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) :
    AEStronglyMeasurable (fun x => inner ℝ
      (GlobalMetricCoefficient.CM.Construction.varietyGlobalMetricCoefficient V C b x (GlobalLp.CM.Construction.varietyOneFormField V C b form x))
      (GlobalLp.CM.Construction.varietyOneFormField V C b other x)) (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) := by
  have hA := GlobalMetricCoefficient.CM.Construction.varietyGlobalMetricCoefficient_measurable V C b
  have hF := (GlobalLp.CM.Construction.varietyOneFormField_memLp V C b form).aestronglyMeasurable
  have hG := (GlobalLp.CM.Construction.varietyOneFormField_memLp V C b other).aestronglyMeasurable
  have hAF := (ContinuousLinearMap.id ℝ (EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)).aestronglyMeasurable_comp₂ hA hF
  exact (innerSL ℝ).aestronglyMeasurable_comp₂ hAF hG

theorem varietySmoothEnergy_integral_chart (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V) (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (form other : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1)
    (hother : ∀ x, x ∉ e.source → other x = 0) :
    (∫ x, inner ℝ (GlobalMetricCoefficient.CM.Construction.varietyGlobalMetricCoefficient V C b x (GlobalLp.CM.Construction.varietyOneFormField V C b form x))
      (GlobalLp.CM.Construction.varietyOneFormField V C b other x) ∂ GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) =
    ∫ z in (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)),
      inner ℝ (MetricDirichlet.CM.Construction.varietyComplexDirichletOperator V e b z
        (GlobalLp.CM.Construction.varietyOneFormInChart V b e form (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))))
        (GlobalLp.CM.Construction.varietyOneFormInChart V b e other (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))) := by
  let f := fun x => inner ℝ (GlobalMetricCoefficient.CM.Construction.varietyGlobalMetricCoefficient V C b x (GlobalLp.CM.Construction.varietyOneFormField V C b form x))
    (GlobalLp.CM.Construction.varietyOneFormField V C b other x)
  have hzero : ∀ x, x ∉ e.source → f x = 0 := by
    intro x hx
    dsimp only [f]
    rw [ChartTestDifferential.CM.Construction.varietyOneFormField_zero_at V C b other (hother x hx), inner_zero_right]
  calc
    _ = ∫ x in e.source, f x ∂ GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    _ = ∫ z in (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)),
        Metric.CM.Construction.varietyMetricDensity V e z • f (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) :=
      MetricBochnerIntegration.CM.Construction.varietyMetricMeasure_integral_chart V e he f (varietySmoothEnergy_aestronglyMeasurable V C b form other)
    _ = _ := by
      apply setIntegral_congr_fun (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.measurableSet
      intro z hz
      dsimp only [f]
      rw [MetricEnergyInvariant.CM.Construction.varietyGlobalMetricCoefficient_form_energy V C b e he form other (e.map_target hz),
        e.right_inv hz, ContinuousLinearEquiv.symm_apply_apply, MetricNormalization.CM.Construction.varietyComplexDirichletOperator_density,
        smul_apply, real_inner_smul_left, smul_eq_mul]

theorem varietySmoothEnergy_chart_test (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V) (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1)
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    (∫ x, inner ℝ (GlobalMetricCoefficient.CM.Construction.varietyGlobalMetricCoefficient V C b x (GlobalLp.CM.Construction.varietyOneFormField V C b form x))
      (GlobalLp.CM.Construction.varietyOneFormField V C b (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (ChartTestFunction.CM.Construction.varietyChartTestForm V e he g hgc hg)) x)
      ∂ GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) =
    ∫ z in (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)),
      inner ℝ (MetricDirichlet.CM.Construction.varietyComplexDirichletOperator V e b z
        (GlobalLp.CM.Construction.varietyOneFormInChart V b e form (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))))
        (GlobalLp.CM.Construction.varietyOneFormInChart V b e (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (ChartTestFunction.CM.Construction.varietyChartTestForm V e he g hgc hg))
          (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))) := by
  apply varietySmoothEnergy_integral_chart V C b e he
  intro x hx
  exact ChartTestDifferential.CM.Construction.varietyChartTestForm_d_zero V e he g hgc hg
    (fun h => hx (ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_subset_source V e hg h))

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothEnergyChart.CM.Construction

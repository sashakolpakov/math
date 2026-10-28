import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothEnergyChart
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartGradientIdentity

/-! # Smooth Energy Cutoff -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothEnergyCutoff.CM.Construction

noncomputable section

/-! Inserting a cutoff equal to one near a test function changes neither
the actual global energy nor its Euclidean gradient expression. -/

open Set _root_.MeasureTheory Filter
open scoped SchwartzMap _root_.Topology

variable {ι : Type*} [Fintype ι]

theorem varietySmoothEnergy_cutoff_gradient (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V) (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0)
    (g η : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ))
    (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hgU : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (hηc : HasCompactSupport (η : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hηU : tsupport η ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (hη : ∀ z ∈ tsupport g, (η : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ) =ᶠ[𝓝 z] 1)
    (A : EuclideanMetric.CM.Construction.varietyEuclideanModel V → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (hA : ∀ z ∈ tsupport g, A z = MetricDirichlet.CM.Construction.varietyComplexDirichletOperator V e b z) :
    (∫ x, inner ℝ (GlobalMetricCoefficient.CM.Construction.varietyGlobalMetricCoefficient V C b x
        (GlobalLp.CM.Construction.varietyOneFormField V C b (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f) x))
      (GlobalLp.CM.Construction.varietyOneFormField V C b (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (ChartTestFunction.CM.Construction.varietyChartTestForm V e he g hgc hgU)) x)
      ∂ GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) =
    ∫ z, inner ℝ (A z (SchwartzGradient.CM.Construction.schwartzOrdinaryGradient b (ScalarChartLocalization.CM.Construction.varietyScalarChartCutoff V e he η hηc hηU f) z))
      (SchwartzGradient.CM.Construction.schwartzOrdinaryGradient b g z) := by
  rw [SmoothEnergyChart.CM.Construction.varietySmoothEnergy_chart_test V C b e he (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f) g hgc hgU]
  calc
    _ = ∫ z in (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)),
        inner ℝ (A z (SchwartzGradient.CM.Construction.schwartzOrdinaryGradient b (ScalarChartLocalization.CM.Construction.varietyScalarChartCutoff V e he η hηc hηU f) z))
          (SchwartzGradient.CM.Construction.schwartzOrdinaryGradient b g z) := by
      apply setIntegral_congr_fun (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.measurableSet
      intro z hz
      dsimp only
      rw [ChartGradientIdentity.CM.Construction.varietyChartTestForm_gradient V e he b g hgc hgU hz]
      by_cases hzg : z ∈ tsupport g
      · rw [hA z hzg, ChartGradientIdentity.CM.Construction.varietyScalarChartCutoff_gradient_locally_one V e he b η hηc hηU f hz (hη z hzg)]
      · rw [SchwartzGradient.CM.Construction.schwartzOrdinaryGradient_zero b g hzg, inner_zero_right, inner_zero_right]
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      rw [SchwartzGradient.CM.Construction.schwartzOrdinaryGradient_zero b g (fun h => hz (hgU h)), inner_zero_right])

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothEnergyCutoff.CM.Construction

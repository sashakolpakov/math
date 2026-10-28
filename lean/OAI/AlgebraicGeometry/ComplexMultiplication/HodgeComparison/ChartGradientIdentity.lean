import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartTestDifferential
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartCutoffDerivative
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SchwartzGradient

/-! # Chart Gradient Identity -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartGradientIdentity.CM.Construction

noncomputable section

/-! Ordinary chart gradients agree with global exterior derivatives, and
an auxiliary cutoff equal to one near a test support preserves that gradient. -/

open Set Filter
open scoped SchwartzMap LineDeriv _root_.Topology

variable {ι : Type*} [Fintype ι]

theorem varietyChartTestForm_gradient (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    GlobalLp.CM.Construction.varietyOneFormInChart V b e (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (ChartTestFunction.CM.Construction.varietyChartTestForm V e he g hgc hg))
      (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) = SchwartzGradient.CM.Construction.schwartzOrdinaryGradient b g z := by
  apply PiLp.ext
  intro i
  rw [SchwartzGradient.CM.Construction.schwartzOrdinaryGradient_apply]
  exact ChartTestDifferential.CM.Construction.varietyChartTestForm_derivative V e he b g hgc hg hz i

theorem varietyScalarChartCutoff_gradient_locally_one (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (η : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hηc : HasCompactSupport (η : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hηU : tsupport η ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0)
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (hη : (η : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ) =ᶠ[𝓝 z] 1) :
    SchwartzGradient.CM.Construction.schwartzOrdinaryGradient b (ScalarChartLocalization.CM.Construction.varietyScalarChartCutoff V e he η hηc hηU f) z =
      GlobalLp.CM.Construction.varietyOneFormInChart V b e (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f) (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) := by
  apply PiLp.ext
  intro i
  rw [SchwartzGradient.CM.Construction.schwartzOrdinaryGradient_apply, ChartCutoffDerivative.CM.Construction.varietyScalarChartCutoff_derivative V e he b η hηc hηU f hz i]
  have hd : (∂_{b i} η : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) z = 0 := by
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, hη.fderiv_eq]
    change fderiv ℝ (Function.const (EuclideanMetric.CM.Construction.varietyEuclideanModel V) (1 : ℂ)) z (b i) = 0
    rw [fderiv_const]
    rfl
  rw [hd, hη.eq_of_nhds]
  simp only [Pi.one_apply, zero_mul, one_mul, zero_add]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartGradientIdentity.CM.Construction

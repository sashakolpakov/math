import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.RescalePair
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.EnergyCoercivity
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Potential

/-! # Weighted Norm -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.WeightedNorm

noncomputable section

/-! The actual completed bundle norm for a modified metric is precisely its weighted original metric integral. -/

open _root_.MeasureTheory
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)

theorem holomorphicMetric_rescale_norm_sq (f : V.analyticSpace → ℝ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ) ∞ f) (hp : ∀ x, 0 < f x)
    (n : ℕ) (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    ‖IntegralPairZero.holomorphicFormL2WithInclusion V (h.rescale f hf hp) n a‖ ^ 2 =
      ∫ x, f x * (h.globalFormPair V n a a x).re ∂(ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) :=
  (IntegralPairZero.holomorphicFormL2WithInclusion_norm_sq V (h.rescale f hf hp) n a).trans
    (h.rescale_formIntegralPair_re V f hf hp n a a)

theorem holomorphicMetric_withPotential_norm_sq (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0)
    (n : ℕ) (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    ‖IntegralPairZero.holomorphicFormL2WithInclusion V (h.withPotential f) n a‖ ^ 2 =
      ∫ x, Real.exp (ScalarPotentialFunctions.realPotentialScalar f x) * (h.globalFormPair V n a a x).re ∂(ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) :=
  holomorphicMetric_rescale_norm_sq V h _ _ _ n a

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.WeightedNorm

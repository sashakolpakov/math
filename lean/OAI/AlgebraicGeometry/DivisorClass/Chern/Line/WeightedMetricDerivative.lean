import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.ConnectionOperator
import OAI.Analysis.HodgeTheory.Decomposition.MetricDensityDerivative

/-! # Weighted Metric Derivative -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Line.WeightedMetricDerivative

noncomputable section

/-! The actual line and volume weighted metric derivative for two varying covector fields. -/

open scoped ComplexConjugate
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.Analysis.HodgeTheory.Decomposition.MetricDensityDerivative.Constructions

attribute [local instance] Analysis.HodgeTheory.Decomposition.BilinearMetricDifferential.Constructions.metricDifferentialBilinearNormed Analysis.HodgeTheory.Decomposition.BilinearMetricDifferential.Constructions.metricDifferentialBilinearNormedSpace
  Analysis.HodgeTheory.Decomposition.BilinearMetricDifferential.Constructions.metricDifferentialCovectorPairNormedSpace

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

theorem lineWeightedMetricPair_derivative (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E)
    (A : E → E →L[ℝ] ℂ) (w : E → ℂ) (a c : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x v : E)
    (hB : DifferentiableAt ℝ B x) (hw : DifferentiableAt ℝ w x)
    (ha : DifferentiableAt ℝ a x) (hc : DifferentiableAt ℝ c x)
    (hρ : DifferentiableAt ℝ (fun y => ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B y)) x)
    (hBs : ∀ u t, B x u t = B x t u) (hpos : ∀ u : E, u ≠ 0 → 0 < B x u u)
    (hG : ∀ u t, B x (G x v u) t + B x u (G x v t) = fderiv ℝ B x v u t)
    (hA : fderiv ℝ w x v = w x * (conj (A x v) + A x v)) :
    fderiv ℝ (fun y => (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B y) : ℂ) *
      (w y * Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B y) (a y) (c y))) x v =
      (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B x) : ℂ) * w x *
        (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x) (ConnectionSymbols.lineCovectorConnectionDerivative n G A a x v) (c x) +
          Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x) (a x) (ConnectionSymbols.lineCovectorConnectionDerivative n G A c x v) +
          (LinearMap.toMatrix b b (G x v).toLinearMap).trace • Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x) (a x) (c x)) := by
  have hp := Analysis.HodgeTheory.Decomposition.WeightedMetricDerivative.Constructions.bilinearFormMetricPair_differentiableAt b n B a c hB ha hc
    (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearExteriorGram_det_ne_zero b n (B x) hBs hpos)
  have hρc := Complex.ofRealCLM.hasFDerivAt.comp x hρ.hasFDerivAt
  have hd := congrArg (fun L : E →L[ℝ] ℂ => L v) (hρc.mul (hw.mul hp).hasFDerivAt).fderiv
  change fderiv ℝ (fun y => (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B y) : ℂ) *
    (w y * Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B y) (a y) (c y))) x v = _ at hd
  simp only [_root_.add_apply, _root_.smul_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, smul_eq_mul, Pi.mul_def, Function.comp_def] at hd
  rw [ConnectionOperator.lineMetricPair_covariant_derivative b n B G A w a c x v hB hw ha hc hBs hpos hG hA,
    Analysis.HodgeTheory.Decomposition.MetricDensityDerivative.Constructions.metricDensity_fderiv_connection b B hB hBs hpos v (G x v) hG] at hd
  rw [hd]
  simp only [Complex.ofReal_mul, RCLike.real_smul_eq_coe_mul]
  ring_nf
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Line.WeightedMetricDerivative

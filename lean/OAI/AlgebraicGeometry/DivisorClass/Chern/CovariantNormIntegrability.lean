import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.RoughDivergence
import OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.NormIntegral

/-! # Covariant Norm Integrability -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CovariantNormIntegrability

noncomputable section

/-! Support and integration estimates for the ordinary norm of an actual covariant derivative. -/

open _root_.MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Line.HessianBilinear.tensorConnection_formNormed Line.HessianBilinear.tensorConnection_formSpace
  Line.HessianBilinear.tensorConnection_oneNormed Line.HessianBilinear.tensorConnection_oneSpace
  Line.RoughSmooth.roughSmooth_metricNormed Line.RoughSmooth.roughSmooth_metricSpace Line.RoughSmooth.roughSmooth_connectionNormed Line.RoughSmooth.roughSmooth_connectionSpace

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

omit [Fintype ι] [LinearOrder ι] [FiniteDimensional ℝ E] in
theorem lineCovectorConnectionDerivative_norm_sq_integrable (n : ℕ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    {U : Set E} (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) (hA : ContDiffOn ℝ ∞ A U)
    (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a) (hs : tsupport a ⊆ U) :
    Integrable (fun x => ‖Line.ConnectionSymbols.lineCovectorConnectionDerivative n G A a x‖ ^ 2) μ := by
  let M := Line.ConnectionSymbols.lineCovectorConnectionDerivative n G A a
  have hM : ContDiff ℝ ∞ M := CovectorConnectionSupport.lineCovectorConnectionDerivative_global_smooth n G A a hU hG hA ha hs
  have hc : HasCompactSupport M := hac.isCompact.of_isClosed_subset (isClosed_tsupport M)
    (CovectorConnectionSupport.lineCovectorConnectionDerivative_tsupport n G A a)
  exact Compact.NormIntegral.compact_norm_sq_integrable μ M hM.continuous hc

omit μ [Measure.IsAddHaarMeasure μ] [MeasurableSpace E] [BorelSpace E] in
theorem lineCovectorFullEnergy_norm_lower_of_support (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (w : E → ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) {T : Set E} {c : ℝ} (hs : tsupport a ⊆ T)
    (hb : ∀ x ∈ T, ∀ N : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n,
      c * ‖N‖ ^ 2 ≤ ((ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B x) : ℂ) * w x * CovectorTensorAlgebra.covectorTensorMetricPair b n (B x) N N).re) :
    ∀ x, c * ‖Line.ConnectionSymbols.lineCovectorConnectionDerivative n G A a x‖ ^ 2 ≤ (Line.RoughDivergence.lineCovectorFullEnergy b n B G A w a x).re := by
  intro x
  by_cases hx : x ∈ T
  · exact hb x hx _
  · have hm : Line.ConnectionSymbols.lineCovectorConnectionDerivative n G A a x = 0 := by
      apply ContinuousLinearMap.ext
      intro v
      exact Line.TensorIntegration.lineCovectorConnectionDerivative_off_support n G A a (fun ht => hx (hs ht)) v
    simp only [Line.RoughDivergence.lineCovectorFullEnergy, hm, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
      CovectorTensorAlgebra.covectorTensorMetricPair, _root_.zero_apply, Analysis.HodgeTheory.Decomposition.BilinearMetricInner.Constructions.bilinearFormMetricPair_eq_inner, map_zero,
      inner_zero_right, Finset.sum_const_zero, Complex.zero_re, le_refl]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CovariantNormIntegrability

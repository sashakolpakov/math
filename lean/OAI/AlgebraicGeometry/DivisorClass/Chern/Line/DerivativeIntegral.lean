import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.CovectorConnectionOperator
import OAI.AlgebraicGeometry.DivisorClass.Chern.CovariantNormIntegrability

/-! # Derivative Integral -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Line.DerivativeIntegral

noncomputable section

/-! Integrated ordinary first-derivative control from the actual covariant derivative and connection coefficients. -/

open _root_.MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] HessianBilinear.tensorConnection_formNormed HessianBilinear.tensorConnection_formSpace
  HessianBilinear.tensorConnection_oneNormed HessianBilinear.tensorConnection_oneSpace
  CovectorConnectionOperator.lineOperator_endNormed CovectorConnectionOperator.lineOperator_endSpace CovectorConnectionOperator.lineOperator_directionNormed CovectorConnectionOperator.lineOperator_directionSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [Measure.IsAddHaarMeasure μ]

theorem lineCovectorDerivative_direction_integral (n : ℕ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    {U T : Set E} (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) (hA : ContDiffOn ℝ ∞ A U)
    (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a) (hs : tsupport a ⊆ T) (hTU : T ⊆ U)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x ∈ T, ‖CovectorConnectionOperator.lineCovectorConnectionOperator n (G x) (A x)‖ ≤ C)
    (v : E) (hv : ‖v‖ = 1) :
    (∫ x, ‖fderiv ℝ a x v‖ ^ 2 ∂μ) ≤
      2 * (∫ x, ‖ConnectionSymbols.lineCovectorConnectionDerivative n G A a x‖ ^ 2 ∂μ) +
        (2 * C ^ 2) * ∫ x, ‖a x‖ ^ 2 ∂μ := by
  have hi := Compact.NormIntegral.compact_norm_sq_integrable μ (fun x => fderiv ℝ a x v)
    ((ha.continuous_fderiv (by simp)).clm_apply continuous_const) (hac.fderiv_apply ℝ v)
  have hm := CovariantNormIntegrability.lineCovectorConnectionDerivative_norm_sq_integrable μ n G A a hU hG hA ha hac (hs.trans hTU)
  have hia := Compact.NormIntegral.compact_norm_sq_integrable μ a ha.continuous hac
  have hp (x : E) : ‖fderiv ℝ a x v‖ ^ 2 ≤
      2 * ‖ConnectionSymbols.lineCovectorConnectionDerivative n G A a x‖ ^ 2 + (2 * C ^ 2) * ‖a x‖ ^ 2 := by
    by_cases hx : x ∈ T
    · exact CovectorConnectionOperator.lineCovectorDerivative_unit_sq n G A a x v hv hC (hb x hx)
    · rw [fderiv_of_notMem_tsupport ℝ (fun ht => hx (hs ht)), _root_.zero_apply, norm_zero,
        zero_pow (by decide : 2 ≠ 0)]
      positivity
  have hh := integral_mono hi ((hm.const_mul 2).add (hia.const_mul (2 * C ^ 2))) hp
  simp only [Pi.add_apply] at hh
  rw [integral_add (hm.const_mul 2) (hia.const_mul (2 * C ^ 2)), integral_const_mul, integral_const_mul] at hh
  exact hh

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Line.DerivativeIntegral

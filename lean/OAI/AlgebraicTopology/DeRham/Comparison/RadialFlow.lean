import OAI.AlgebraicTopology.DeRham.Comparison.RadialOne
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Radial Flow -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.RadialFlow

noncomputable section

/-!
# Fundamental theorem of calculus along radial dilations

The endpoint identity below supplies the analytic right-hand side of the
all-degree radial homotopy formula.
-/

open _root_.MeasureTheory
open scoped Interval

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {n : ℕ}

/-- The derivative of the degree-weighted form along a radial dilation. -/
def radialFlowDerivative (form : E → E [⋀^Fin (n + 1)]→L[ℝ] F)
    (x : E) (t : ℝ) : E [⋀^Fin (n + 1)]→L[ℝ] F :=
  ((n + 1 : ℝ) * t ^ n) • form (t • x) +
    t ^ (n + 1) • fderiv ℝ form (t • x) x

private theorem hasDerivAt_weightedRadial (degree : ℕ)
    {form : E → F} {x : E} {t : ℝ}
    (hform : DifferentiableAt ℝ form (t • x)) :
    HasDerivAt (fun s : ℝ ↦ s ^ (degree + 1) • form (s • x))
      (((degree + 1 : ℝ) * t ^ degree) • form (t • x) +
        t ^ (degree + 1) • fderiv ℝ form (t • x) x) t := by
  have hcomp := hform.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const x)
  simpa [Function.comp_def, Pi.smul_def', add_comm] using
    (hasDerivAt_pow (degree + 1) t).smul hcomp

theorem continuous_radialFlowDerivative
    {form : E → E [⋀^Fin (n + 1)]→L[ℝ] F} (hform : ContDiff ℝ 1 form) (x : E) :
    Continuous (radialFlowDerivative form x) := by
  have hradial : Continuous (fun t : ℝ ↦ t • x) :=
    continuous_id.smul continuous_const
  exact ((continuous_const.mul (continuous_pow n)).smul (hform.continuous.comp hradial)).add
    ((continuous_pow (n + 1)).smul
      (((hform.continuous_fderiv (by norm_num)).comp hradial).clm_apply continuous_const))

variable [CompleteSpace F]

private theorem integral_weightedRadial (degree : ℕ)
    {form : E → F} (hform : ContDiff ℝ 1 form) (x : E) :
    (∫ t in (0 : ℝ)..1,
      ((degree + 1 : ℝ) * t ^ degree) • form (t • x) +
        t ^ (degree + 1) • fderiv ℝ form (t • x) x) = form x := by
  have hradial : Continuous (fun t : ℝ ↦ t • x) :=
    continuous_id.smul continuous_const
  have hcontinuous : Continuous (fun t : ℝ ↦
      ((degree + 1 : ℝ) * t ^ degree) • form (t • x) +
        t ^ (degree + 1) • fderiv ℝ form (t • x) x) :=
    ((continuous_const.mul (continuous_pow degree)).smul (hform.continuous.comp hradial)).add
      ((continuous_pow (degree + 1)).smul
        (((hform.continuous_fderiv (by norm_num)).comp hradial).clm_apply continuous_const))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1)
    (fun t _ ↦ hasDerivAt_weightedRadial degree
      (hform.differentiable (by norm_num) (t • x)))
    (hcontinuous.intervalIntegrable 0 1)
  simpa using h

/-- Integrating the radial derivative gives the original positive-degree form. -/
theorem integral_radialFlowDerivative
    {form : E → E [⋀^Fin (n + 1)]→L[ℝ] F} (hform : ContDiff ℝ 1 form) (x : E) :
    (∫ t in (0 : ℝ)..1, radialFlowDerivative form x t) = form x := by
  exact integral_weightedRadial n hform x

end

end OAI.AlgebraicTopology.DeRham.Comparison.RadialFlow

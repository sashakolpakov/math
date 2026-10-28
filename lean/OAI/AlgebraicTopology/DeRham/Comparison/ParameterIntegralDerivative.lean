import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Parameter Integral Derivative -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.ParameterIntegralDerivative

noncomputable section

/-!
# Differentiating a compact-interval integral in a finite-dimensional parameter

Joint C¹ regularity provides the derivative bound on a compact product of a
closed parameter ball and the integration interval. No bound or integral
interchange is assumed as an additional mathematical hypothesis.
-/

open _root_.MeasureTheory Set Filter _root_.Metric
open scoped _root_.Topology Interval

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A jointly C¹ function has a continuous derivative in the parameter direction. -/
theorem continuous_parameterFDeriv {f : E × ℝ → F} (hf : ContDiff ℝ 1 f) :
    Continuous (fun z : E × ℝ => fderiv ℝ (fun y : E => f (y, z.2)) z.1) := by
  have hEq : (fun z : E × ℝ => fderiv ℝ (fun y : E => f (y, z.2)) z.1) =
      fun z => (fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ E ℝ) := by
    funext z
    exact ((hf.differentiable_one z).hasFDerivAt.comp z.1
      (hasFDerivAt_prodMk_left z.1 z.2)).fderiv
  rw [hEq]
  exact (hf.continuous_fderiv one_ne_zero).clm_comp continuous_const

/-- The parameter derivative is integrable on every finite time interval. -/
theorem intervalIntegrable_parameterFDeriv {f : E × ℝ → F}
    (hf : ContDiff ℝ 1 f) (x : E) (a b : ℝ) :
    IntervalIntegrable (fun t => fderiv ℝ (fun y : E => f (y, t)) x) volume a b :=
  ((continuous_parameterFDeriv hf).comp
    (continuous_const.prodMk continuous_id)).intervalIntegrable a b

variable [FiniteDimensional ℝ E]

/-- A jointly C¹ integrand can be differentiated under its finite interval
integral. The derivative is the integral of its actual parameter derivatives.
Finite dimensionality is used only to obtain the compact local bound. -/
theorem hasFDerivAt_intervalIntegral_of_contDiff {f : E × ℝ → F}
    (hf : ContDiff ℝ 1 f) (x : E) (a b : ℝ) :
    HasFDerivAt (fun y : E => ∫ t in a..b, f (y, t))
      (∫ t in a..b, fderiv ℝ (fun y : E => f (y, t)) x) x := by
  let D : E × ℝ → E →L[ℝ] F :=
    fun z => fderiv ℝ (fun y : E => f (y, z.2)) z.1
  have hpartial (y : E) (t : ℝ) :
      HasFDerivAt (fun z : E => f (z, t))
        ((fderiv ℝ f (y, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) y :=
    (hf.differentiable_one (y, t)).hasFDerivAt.comp y (hasFDerivAt_prodMk_left y t)
  have hDformula : D = fun z =>
      (fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ E ℝ) := by
    funext z
    exact (hpartial z.1 z.2).fderiv
  have hDcont : Continuous D := by
    rw [hDformula]
    exact (hf.continuous_fderiv one_ne_zero).clm_comp continuous_const
  obtain ⟨C, hC⟩ :=
    ((isCompact_closedBall x (1 : ℝ)).prod
      (isCompact_uIcc : IsCompact (uIcc a b))).exists_bound_of_continuousOn
        hDcont.continuousOn
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun y t => f (y, t)) (F' := fun y t => D (y, t))
    (bound := fun _ => C) (s := ball x 1) (ball_mem_nhds x zero_lt_one)
  · exact Filter.Eventually.of_forall fun y =>
      (hf.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hf.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b
  · exact (hDcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t ht y hy =>
      hC (y, t) ⟨ball_subset_closedBall hy, uIoc_subset_uIcc ht⟩
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun t _ y _ =>
      (hpartial y t).differentiableAt.hasFDerivAt

/-- The derivative formula corresponding to
`hasFDerivAt_intervalIntegral_of_contDiff`. -/
theorem fderiv_intervalIntegral_of_contDiff {f : E × ℝ → F}
    (hf : ContDiff ℝ 1 f) (x : E) (a b : ℝ) :
    fderiv ℝ (fun y : E => ∫ t in a..b, f (y, t)) x =
      ∫ t in a..b, fderiv ℝ (fun y : E => f (y, t)) x :=
  (hasFDerivAt_intervalIntegral_of_contDiff hf x a b).fderiv

end

end OAI.AlgebraicTopology.DeRham.Comparison.ParameterIntegralDerivative

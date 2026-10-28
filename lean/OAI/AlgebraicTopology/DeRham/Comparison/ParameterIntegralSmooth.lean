import OAI.AlgebraicTopology.DeRham.Comparison.ParameterIntegralDerivative
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-! # Parameter Integral Smooth -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.ParameterIntegralSmooth

noncomputable section

/-!
# Smoothness of compact-interval parameter integrals

The proof differentiates the actual integral and inducts on finite derivative
orders. Finite-dimensionality permits testing the derivative in fixed tangent
directions, so the induction keeps the same coefficient space.
-/

open _root_.MeasureTheory
open scoped ContDiff

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Every finite derivative order of an integral of a jointly smooth integrand
exists and is continuous. -/
theorem contDiff_nat_intervalIntegral_of_smooth (n : ℕ) {f : E × ℝ → F}
    (hf : ContDiff ℝ ∞ f) (a b : ℝ) :
    ContDiff ℝ n (fun x : E => ∫ t in a..b, f (x, t)) := by
  induction n generalizing f with
  | zero =>
    have hd : Differentiable ℝ (fun x : E => ∫ t in a..b, f (x, t)) :=
      fun x => (ParameterIntegralDerivative.hasFDerivAt_intervalIntegral_of_contDiff (hf.of_le (by simp)) x a b).differentiableAt
    exact contDiff_zero.mpr hd.continuous
  | succ n ih =>
    simp only [Nat.cast_add, Nat.cast_one]
    rw [contDiff_succ_iff_fderiv_apply]
    refine ⟨?_, by simp, ?_⟩
    · exact fun x =>
        (ParameterIntegralDerivative.hasFDerivAt_intervalIntegral_of_contDiff (hf.of_le (by simp)) x a b).differentiableAt
    · intro v
      let g : E × ℝ → F := fun z => fderiv ℝ f z (v, 0)
      have hg : ContDiff ℝ ∞ g :=
        (contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const
      have hsection (x : E) (t : ℝ) :
          fderiv ℝ (fun y : E => f (y, t)) x =
            (fderiv ℝ f (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ) :=
        ((hf.differentiable (by simp) (x, t)).hasFDerivAt.comp x
          (hasFDerivAt_prodMk_left x t)).fderiv
      have heq : (fun x : E => fderiv ℝ (fun y : E => ∫ t in a..b, f (y, t)) x v) =
          fun x : E => ∫ t in a..b, g (x, t) := by
        funext x
        rw [ParameterIntegralDerivative.fderiv_intervalIntegral_of_contDiff (hf.of_le (by simp)) x a b,
          ContinuousLinearMap.intervalIntegral_apply
            (ParameterIntegralDerivative.intervalIntegrable_parameterFDeriv (hf.of_le (by simp)) x a b) v]
        apply intervalIntegral.integral_congr
        intro t _
        dsimp only
        rw [hsection]
        rfl
      rw [heq]
      exact ih hg

/-- Integrating a jointly smooth function over a fixed compact interval
preserves smoothness in the finite-dimensional parameter. -/
theorem contDiff_intervalIntegral_of_smooth {f : E × ℝ → F}
    (hf : ContDiff ℝ ∞ f) (a b : ℝ) :
    ContDiff ℝ ∞ (fun x : E => ∫ t in a..b, f (x, t)) :=
  contDiff_infty.mpr fun n => contDiff_nat_intervalIntegral_of_smooth n hf a b

end

end OAI.AlgebraicTopology.DeRham.Comparison.ParameterIntegralSmooth

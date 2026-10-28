import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Singular
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.RadialIntegral

/-! The quantitative near-field estimate for the Newtonian Hessian singular integral. -/

noncomputable section
open _root_.MeasureTheory Set Metric
namespace OAI.Analysis.PDE.Schauder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem integrableOn_compensatedNewtonianEntry (f : E → ℝ) (x v w : E)
    (hd : 1 ≤ Module.finrank ℝ E) (hf : Measurable f) {H α : ℝ}
    (hH : 0 ≤ H) (hα : 0 < α)
    (hholder : ∀ y, |f (x - y) - f x| ≤ H * ‖y‖ ^ α)
    (μ : Measure E) [μ.IsAddHaarMeasure] (R : ℝ) :
    IntegrableOn (compensatedNewtonianEntry f x v w) (ball 0 R) μ :=
  ((locallyIntegrable_compensatedNewtonianEntry f x v w hd hf hH hα hholder μ).integrableOn_isCompact
    (isCompact_closedBall 0 R)).mono_set ball_subset_closedBall

theorem compensatedNewtonian_nearField_bound (f : E → ℝ) (x v w : E)
    (hd : 1 ≤ Module.finrank ℝ E) {H α R : ℝ}
    (hH : 0 ≤ H) (hα : 0 < α) (hR : 0 < R)
    (hholder : ∀ y, |f (x - y) - f x| ≤ H * ‖y‖ ^ α)
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    |∫ y in ball (0 : E) R, compensatedNewtonianEntry f x v w y ∂μ| ≤
      H * newtonianSizeConstant (Module.finrank ℝ E) * rieszBallMass μ α *
        R ^ α * ‖v‖ * ‖w‖ := by
  let : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have hg := (integrableOn_riesz_majorant μ hd hα R).const_mul
    (H * newtonianSizeConstant (Module.finrank ℝ E) * ‖v‖ * ‖w‖)
  have hb : ∀ᵐ y ∂μ.restrict (ball (0 : E) R),
      ‖compensatedNewtonianEntry f x v w y‖ ≤
        (H * newtonianSizeConstant (Module.finrank ℝ E) * ‖v‖ * ‖w‖) *
          ‖y‖ ^ (α - (Module.finrank ℝ E : ℝ)) := by
    have hzero : ∀ᵐ y ∂μ, y ≠ (0 : E) := by rw [ae_iff]; simp
    filter_upwards [ae_restrict_of_ae hzero] with y hy
    exact compensatedNewtonianEntry_bound f x v w hH hholder hy
  have hi := norm_integral_le_of_norm_le hg hb
  rw [integral_const_mul, integral_riesz_majorant_ball μ α hR] at hi
  rw [Real.norm_eq_abs] at hi
  convert hi using 1 ; ring

end OAI.Analysis.PDE.Schauder

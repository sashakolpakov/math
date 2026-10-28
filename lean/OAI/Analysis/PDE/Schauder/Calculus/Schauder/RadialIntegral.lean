import Mathlib

/-! Exact scaling of the integrable radial majorants used in the Schauder estimates. -/

noncomputable section
open _root_.MeasureTheory Set Metric
open scoped Pointwise
namespace OAI.Analysis.PDE.Schauder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def rieszBallMass (μ : Measure E) (α : ℝ) : ℝ :=
  ∫ y in ball (0 : E) 1, ‖y‖ ^ (α - (Module.finrank ℝ E : ℝ)) ∂μ

omit [FiniteDimensional ℝ E] [BorelSpace E] in
theorem rieszBallMass_nonneg (μ : Measure E) (α : ℝ) : 0 ≤ rieszBallMass μ α :=
  integral_nonneg fun y => Real.rpow_nonneg (norm_nonneg y) _

theorem integrableOn_riesz_majorant (μ : Measure E) [μ.IsAddHaarMeasure]
    (hd : 1 ≤ Module.finrank ℝ E) {α : ℝ} (hα : 0 < α) (R : ℝ) :
    IntegrableOn (fun y : E => ‖y‖ ^ (α - (Module.finrank ℝ E : ℝ))) (ball 0 R) μ := by
  apply integrableOn_ball_of_norm_le_rpow hd (C := 1)
    (α := (Module.finrank ℝ E : ℝ) - α) (by linarith)
  · filter_upwards with y
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg y) _),
      neg_sub, one_mul]
    exact le_rfl
  · exact (by fun_prop : Measurable (fun y : E => ‖y‖ ^ (α - (Module.finrank ℝ E : ℝ)))).aestronglyMeasurable

theorem integral_riesz_majorant_ball (μ : Measure E) [μ.IsAddHaarMeasure]
    (α : ℝ) {R : ℝ} (hR : 0 < R) :
    (∫ y in ball (0 : E) R, ‖y‖ ^ (α - (Module.finrank ℝ E : ℝ)) ∂μ) =
      R ^ α * rieszBallMass μ α := by
  have he := μ.setIntegral_comp_smul_of_pos
    (fun y : E => ‖y‖ ^ (α - (Module.finrank ℝ E : ℝ))) (ball (0 : E) 1) hR
  have himage : R • ball (0 : E) 1 = ball 0 R := by
    rw [_root_.smul_ball hR.ne', smul_zero, Real.norm_eq_abs, abs_of_pos hR, mul_one]
  have hf (y : E) : ‖R • y‖ ^ (α - (Module.finrank ℝ E : ℝ)) =
      R ^ (α - (Module.finrank ℝ E : ℝ)) * ‖y‖ ^ (α - (Module.finrank ℝ E : ℝ)) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR, Real.mul_rpow hR.le (norm_nonneg y)]
  simp only [himage, hf, integral_const_mul, smul_eq_mul] at he
  have hp : R ^ Module.finrank ℝ E * R ^ (α - (Module.finrank ℝ E : ℝ)) = R ^ α := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hR]
    congr 1
    ring
  have hh := congrArg (fun t : ℝ => R ^ Module.finrank ℝ E * t) he
  rw [← mul_assoc, hp, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hR.ne'), one_mul] at hh
  exact hh.symm

end OAI.Analysis.PDE.Schauder

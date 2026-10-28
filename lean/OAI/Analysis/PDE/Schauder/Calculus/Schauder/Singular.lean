import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Newtonian

/-! The Hölder cancellation that makes the Newtonian second-derivative kernel integrable. -/

noncomputable section
open _root_.MeasureTheory Set Metric
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def newtonianSecond (m : ℕ) (y : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (newtonianKernel m)) y

def compensatedNewtonianEntry (f : E → ℝ) (x v w y : E) : ℝ :=
  (f (x - y) - f x) * newtonianSecond (Module.finrank ℝ E) y v w

def newtonianSizeConstant (m : ℕ) : ℝ := |2 - (m : ℝ)| + |(m : ℝ) * ((m : ℝ) - 2)|

theorem newtonianSizeConstant_nonneg (m : ℕ) : 0 ≤ newtonianSizeConstant m :=
  add_nonneg (abs_nonneg _) (abs_nonneg _)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem newtonianEntry_bound (m : ℕ) {y : E} (hy : y ≠ 0) (v w : E) :
    |newtonianSecond m y v w| ≤ newtonianSizeConstant m * ‖y‖ ^ (-(m : ℝ)) * ‖v‖ * ‖w‖ := by
  rw [← Real.norm_eq_abs]
  calc
    _ ≤ ‖newtonianSecond m y v‖ * ‖w‖ := (newtonianSecond m y v).le_opNorm w
    _ ≤ (‖newtonianSecond m y‖ * ‖v‖) * ‖w‖ :=
      mul_le_mul_of_nonneg_right ((newtonianSecond m y).le_opNorm v) (norm_nonneg w)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (newtonianKernel_second_fderiv_norm_le m hy) (norm_nonneg v))
      (norm_nonneg w)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem compensatedNewtonianEntry_bound (f : E → ℝ) (x v w : E) {H α : ℝ}
    (hH : 0 ≤ H) (hf : ∀ y, |f (x - y) - f x| ≤ H * ‖y‖ ^ α)
    {y : E} (hy : y ≠ 0) :
    ‖compensatedNewtonianEntry f x v w y‖ ≤ H * newtonianSizeConstant (Module.finrank ℝ E) * ‖v‖ * ‖w‖ *
      ‖y‖ ^ (α - (Module.finrank ℝ E : ℝ)) := by
  have hK := newtonianEntry_bound (Module.finrank ℝ E) hy v w
  rw [compensatedNewtonianEntry, Real.norm_eq_abs, abs_mul]
  calc
    _ ≤ (H * ‖y‖ ^ α) *
        (newtonianSizeConstant (Module.finrank ℝ E) * ‖y‖ ^ (-(Module.finrank ℝ E : ℝ)) * ‖v‖ * ‖w‖) :=
      mul_le_mul (hf y) hK (abs_nonneg _) (mul_nonneg hH (Real.rpow_nonneg (norm_nonneg _) _))
    _ = _ := by
      rw [show α - (Module.finrank ℝ E : ℝ) = α + -(Module.finrank ℝ E : ℝ) by ring,
        Real.rpow_add (norm_pos_iff.mpr hy)]
      ring

omit [FiniteDimensional ℝ E] in
theorem measurable_newtonianSecond (m : ℕ) : Measurable (newtonianSecond (E := E) m) :=
  measurable_fderiv ℝ _

theorem measurable_compensatedNewtonianEntry (f : E → ℝ) (hf : Measurable f) (x v w : E) :
    Measurable (compensatedNewtonianEntry f x v w) :=
  ((hf.comp (measurable_const.sub measurable_id)).sub measurable_const).mul
    ((ContinuousLinearMap.measurable_apply w).comp
      ((ContinuousLinearMap.measurable_apply v).comp (measurable_newtonianSecond _)))

/-- This statement supplies the genuine Bochner integrability needed before differentiating a
Newtonian potential. The only regularity premise on the data is its stated Hölder increment bound. -/
theorem locallyIntegrable_compensatedNewtonianEntry (f : E → ℝ) (x v w : E)
    (hd : 1 ≤ Module.finrank ℝ E) (hf : Measurable f) {H α : ℝ}
    (hH : 0 ≤ H) (hα : 0 < α)
    (hholder : ∀ y, |f (x - y) - f x| ≤ H * ‖y‖ ^ α)
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    LocallyIntegrable (compensatedNewtonianEntry f x v w) μ := by
  let : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  apply locallyIntegrable_of_norm_le_rpow hd
    (α := (Module.finrank ℝ E : ℝ) - α)
    (C := H * newtonianSizeConstant (Module.finrank ℝ E) * ‖v‖ * ‖w‖) (by linarith)
  · have hzero : ∀ᵐ y ∂μ, y ≠ (0 : E) := by rw [ae_iff]; simp
    filter_upwards [hzero] with y hy
    simpa only [neg_sub] using compensatedNewtonianEntry_bound f x v w hH hholder hy
  · exact (measurable_compensatedNewtonianEntry f hf x v w).aestronglyMeasurable

end OAI.Analysis.PDE.Schauder

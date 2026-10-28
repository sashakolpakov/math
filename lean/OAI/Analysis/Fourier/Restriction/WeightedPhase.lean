import OAI.Analysis.Fourier.Restriction.Basic

open _root_.MeasureTheory Set Filter
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem weighted_small_phase_lower {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {w θ : X → ℝ} (hw : Integrable w μ) (hw0 : ∀ x, 0 ≤ w x) (hθ : Measurable θ)
    (hsmall : ∀ x, w x ≠ 0 → |θ x| ≤ 1 / 4) :
    (∫ x, w x ∂μ) / 2 ≤ ‖∫ x, Complex.exp (Complex.I * (θ x : ℂ)) * (w x : ℂ) ∂μ‖ := by
  have hm : AEStronglyMeasurable (fun x ↦ Complex.exp (Complex.I * (θ x : ℂ)) * (w x : ℂ)) μ := by
    exact (((Complex.measurable_ofReal.comp hθ).const_mul Complex.I).cexp.aestronglyMeasurable).mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hw.aestronglyMeasurable)
  have hi : Integrable (fun x ↦ Complex.exp (Complex.I * (θ x : ℂ)) * (w x : ℂ)) μ := by
    apply hw.mono' hm
    filter_upwards [] with x
    simp [Complex.norm_exp, abs_of_nonneg (hw0 x)]
  have hl (x : X) : (1 / 2 : ℝ) * w x ≤
      (Complex.exp (Complex.I * (θ x : ℂ)) * (w x : ℂ)).re := by
    by_cases hx : w x = 0
    · simp [hx]
    · have hb := abs_le.mp (hsmall x hx)
      have hc := Real.one_sub_sq_div_two_le_cos (x := θ x)
      have hcos : (1 / 2 : ℝ) ≤ Real.cos (θ x) := by nlinarith
      have he : (Complex.exp (Complex.I * (θ x : ℂ)) * (w x : ℂ)).re =
          Real.cos (θ x) * w x := by simp [Complex.mul_re, Complex.exp_re]
      rw [he]
      exact mul_le_mul_of_nonneg_right hcos (hw0 x)
  calc
    _ = ∫ x, (1 / 2 : ℝ) * w x ∂μ := by rw [integral_const_mul]; ring
    _ ≤ ∫ x, (Complex.exp (Complex.I * (θ x : ℂ)) * (w x : ℂ)).re ∂μ :=
      integral_mono (hw.const_mul _) hi.re hl
    _ = (∫ x, Complex.exp (Complex.I * (θ x : ℂ)) * (w x : ℂ) ∂μ).re := integral_re hi
    _ ≤ _ := Complex.re_le_norm _

end OAI.Analysis.Fourier.Restriction

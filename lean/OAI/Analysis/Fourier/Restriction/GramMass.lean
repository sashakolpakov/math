import OAI.Analysis.Fourier.Restriction.GramKernel

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem lintegral_gramKernel_le_of_row_column
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [SFinite μ] (ν : Measure Y) [SFinite ν]
    {K : Y × X → ℂ} (hK : Measurable K) {A B : ℝ≥0∞}
    (hrow : ∀ y, (∫⁻ z, ‖K (y, z)‖ₑ ∂μ) ≤ B)
    (hcol : ∀ x, (∫⁻ y, ‖K (y, x)‖ₑ ∂ν) ≤ A) (x : X) :
    (∫⁻ z, ‖gramKernel ν K (x, z)‖ₑ ∂μ) ≤ B * A := by
  have hm : Measurable (fun w : X × Y ↦ ‖K (w.2, x)‖ₑ * ‖K (w.2, w.1)‖ₑ) := by
    fun_prop
  have hx : Measurable (fun y ↦ ‖K (y, x)‖ₑ) := by fun_prop
  calc
    _ ≤ ∫⁻ z, ∫⁻ y, ‖K (y, x)‖ₑ * ‖K (y, z)‖ₑ ∂ν ∂μ := by
      apply lintegral_mono
      intro z
      simpa only [gramKernel, ← ofReal_norm, norm_mul, norm_star,
        ENNReal.ofReal_mul (norm_nonneg _)] using
        enorm_integral_le_lintegral_enorm (μ := ν) (fun y ↦ K (y, x) * star (K (y, z)))
    _ = ∫⁻ y, ∫⁻ z, ‖K (y, x)‖ₑ * ‖K (y, z)‖ₑ ∂μ ∂ν :=
      lintegral_lintegral_swap hm.aemeasurable
    _ ≤ ∫⁻ y, ‖K (y, x)‖ₑ * B ∂ν := by
      apply lintegral_mono
      intro y
      dsimp only
      rw [lintegral_const_mul _ (by fun_prop)]
      exact mul_le_mul' le_rfl (hrow y)
    _ = B * ∫⁻ y, ‖K (y, x)‖ₑ ∂ν := by
      simp_rw [mul_comm _ B]
      exact lintegral_const_mul B hx
    _ ≤ B * A := mul_le_mul' le_rfl (hcol x)

end OAI.Analysis.Fourier.Restriction

import OAI.Analysis.Fourier.Restriction.Truncation

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem norm_le_threshold_mul_rpow {x t a : ℝ}
    (ht : 0 < t) (htx : t ≤ x) (ha : 1 ≤ a) :
    x ≤ t ^ (1 - a) * x ^ a := by
  have hx : 0 < x := ht.trans_le htx
  have hm := Real.rpow_le_rpow_of_nonpos ht htx (by linarith : 1 - a ≤ 0)
  calc
    x = x ^ (1 - a) * x ^ a := by
      rw [← Real.rpow_add hx, sub_add_cancel, Real.rpow_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg hx.le _)

theorem rpow_le_threshold_mul_rpow {x t a s : ℝ}
    (hx : 0 ≤ x) (hxt : x ≤ t) (ha : 0 < a) (has : a ≤ s) :
    x ^ s ≤ t ^ (s - a) * x ^ a := by
  by_cases hx0 : x = 0
  · subst x
    rw [Real.zero_rpow (by linarith : s ≠ 0), Real.zero_rpow ha.ne', mul_zero]
  · have hx : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    calc
      x ^ s = x ^ (s - a) * x ^ a := by
        rw [← Real.rpow_add hx, sub_add_cancel]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hx.le hxt (sub_nonneg.mpr has)) (Real.rpow_nonneg hx.le _)

theorem lintegral_amplitudeHigh_le_moment
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {f : X → ℂ} (hf : Measurable f) {t a : ℝ} (ht : 0 < t) (ha : 1 ≤ a) :
    (∫⁻ x, ‖amplitudeHigh f t x‖ₑ ∂μ) ≤
      ENNReal.ofReal (t ^ (1 - a)) * ∫⁻ x, ‖f x‖ₑ ^ a ∂μ := by
  rw [← lintegral_const_mul _ (hf.enorm.pow_const a)]
  apply lintegral_mono
  intro x
  by_cases hx : t < ‖f x‖
  · have H := ENNReal.ofReal_le_ofReal (norm_le_threshold_mul_rpow ht hx.le ha)
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _),
      ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by linarith : 0 ≤ a), ofReal_norm] at H
    simpa [amplitudeHigh, hx] using H
  · simp [amplitudeHigh, hx]

theorem lintegral_amplitudeLow_le_moment
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {f : X → ℂ} (hf : Measurable f) {t a s : ℝ}
    (ht : 0 ≤ t) (ha : 0 < a) (has : a ≤ s) :
    (∫⁻ x, ‖amplitudeLow f t x‖ₑ ^ s ∂μ) ≤
      ENNReal.ofReal (t ^ (s - a)) * ∫⁻ x, ‖f x‖ₑ ^ a ∂μ := by
  rw [← lintegral_const_mul _ (hf.enorm.pow_const a)]
  apply lintegral_mono
  intro x
  by_cases hx : ‖f x‖ ≤ t
  · have H := ENNReal.ofReal_le_ofReal (rpow_le_threshold_mul_rpow (norm_nonneg (f x)) hx ha has)
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg ht _),
      ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by linarith : 0 ≤ s),
      ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ha.le, ofReal_norm] at H
    simpa [amplitudeLow, hx] using H
  · simp [amplitudeLow, hx, show 0 < s by linarith]

end OAI.Analysis.Fourier.Restriction

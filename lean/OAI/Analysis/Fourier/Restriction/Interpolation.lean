import OAI.Analysis.Fourier.BochnerRiesz.FourierLimit

open _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

/-- Interpolation of a finite `Lp` norm with a pointwise uniform bound.
The measure space need not have finite total measure. -/
theorem eLpNorm_le_of_enorm_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f : X → ℂ} (hf : AEStronglyMeasurable f μ)
    {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q)
    {B : ℝ≥0∞} (hB : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ B) :
    eLpNorm f (ENNReal.ofReal q) μ ≤
      B ^ ((q - p) / q) * eLpNorm f (ENNReal.ofReal p) μ ^ (p / q) := by
  have hq : 0 < q := hp.trans_le hpq
  have hdiff : 0 ≤ q - p := sub_nonneg.mpr hpq
  have H : eLpNorm f (ENNReal.ofReal q) μ ^ q ≤
      B ^ (q - p) * eLpNorm f (ENNReal.ofReal p) μ ^ p := by
    rw [OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_rpow_eq_lintegral hq hf, OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_rpow_eq_lintegral hp hf,
      ← lintegral_const_mul'' _ (hf.enorm.pow_const p)]
    apply lintegral_mono_ae
    filter_upwards [hB] with x hx
    calc
      ‖f x‖ₑ ^ q = ‖f x‖ₑ ^ (q - p) * ‖f x‖ₑ ^ p := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ hdiff hp.le]
        congr 1
        ring
      _ ≤ B ^ (q - p) * ‖f x‖ₑ ^ p := by
        exact mul_le_mul (ENNReal.rpow_le_rpow hx hdiff) le_rfl zero_le zero_le
  have H' := ENNReal.rpow_le_rpow H (le_of_lt (one_div_pos.mpr hq))
  rw [← ENNReal.rpow_mul, mul_one_div_cancel hq.ne', ENNReal.rpow_one,
    ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt (one_div_pos.mpr hq)),
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at H'
  simpa only [div_eq_mul_inv, one_mul] using H'

end OAI.Analysis.Fourier.Restriction

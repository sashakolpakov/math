import OAI.Analysis.Fourier.WavePackets.Young
import OAI.Analysis.Fourier.Restriction.IntegralKernel
import OAI.Analysis.Fourier.BochnerRiesz.FourierLimit

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

/-- Averaging against a probability measure contracts every finite
Lp norm. This form allows infinite norms and imposes no prior membership
assumption on the averaged function. -/
theorem eLpNorm_average_rpow_le {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [SFinite μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    {F : X × Y → ℂ} (hF : Measurable F) {p : ℝ} (hp : 1 ≤ p) :
    eLpNorm (fun x ↦ ∫ y, F (x, y) ∂ν) (ENNReal.ofReal p) μ ^ p ≤
      ∫⁻ y, eLpNorm (fun x ↦ F (x, y)) (ENNReal.ofReal p) μ ^ p ∂ν := by
  have hp0 : 0 < p := by linarith
  have hm : AEStronglyMeasurable (fun x ↦ ∫ y, F (x, y) ∂ν) μ :=
    hF.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  rw [OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_rpow_eq_lintegral hp0 hm]
  calc
    _ ≤ ∫⁻ x, ∫⁻ y, ‖F (x, y)‖ₑ ^ p ∂ν ∂μ := by
      apply lintegral_mono
      intro x
      have hx : Measurable (fun y ↦ F (x, y)) :=
        hF.comp (measurable_const.prodMk measurable_id)
      have H := OAI.Analysis.Fourier.WavePackets.lintegral_rpow_le_mass_mul
        (ν := ν) hx.enorm hp
      have HH := ENNReal.rpow_le_rpow
        (enorm_integral_le_lintegral_enorm (μ := ν) (fun y ↦ F (x, y))) hp0.le
      simpa only [measure_univ, ENNReal.one_rpow, one_mul] using HH.trans H
    _ = ∫⁻ y, ∫⁻ x, ‖F (x, y)‖ₑ ^ p ∂μ ∂ν :=
      lintegral_lintegral_swap (hF.enorm.pow_const p).aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro y
      exact (OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_rpow_eq_lintegral hp0
        (hF.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable).symm

end OAI.Analysis.Fourier.Restriction

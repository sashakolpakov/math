import OAI.Analysis.Fourier.SquareFunction.ConvolutionRegularity
import OAI.Analysis.Fourier.WavePackets.Young

open OAI.Analysis.Fourier.Wave

/-! Young's inequality for the Banach-valued kernels used in the
square-function argument. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory
open scoped ENNReal

theorem convolveKernel_commuted {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (K : Space n → H) (f : Space n → ℂ) (x : Space n) :
    convolveKernel K f x = ∫ y, f (x - y) • K y := by
  unfold convolveKernel
  simpa only [sub_sub_cancel] using
    (integral_sub_left_eq_self (fun y => f y • K (x - y)) volume x).symm

theorem eLpNorm_convolveKernel_le {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    {K : Space n → H} {f : Space n → ℂ} (hK : Continuous K)
    (hf : Measurable f) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) :
    eLpNorm (convolveKernel K f) p volume ≤
      eLpNorm K 1 volume * eLpNorm f p volume := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpr : 1 ≤ p.toReal := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_le_toReal ENNReal.one_ne_top hpt).mpr hp
  have hpr0 : 0 < p.toReal := lt_of_lt_of_le zero_lt_one hpr
  have hconv : AEStronglyMeasurable (convolveKernel K f) volume :=
    hf.aestronglyMeasurable.convolution (ContinuousLinearMap.lsmul ℂ ℂ)
      hK.aestronglyMeasurable
  have he : (∫⁻ x, ‖convolveKernel K f x‖ₑ ^ p.toReal) ≤
      (∫⁻ y, ‖K y‖ₑ) ^ p.toReal * ∫⁻ x, ‖f x‖ₑ ^ p.toReal := by
    apply le_trans ?_ (OAI.Analysis.Fourier.WavePackets.lintegral_convolution_rpow_le
      hK.enorm.measurable hf.enorm hpr)
    apply lintegral_mono
    intro x
    apply ENNReal.rpow_le_rpow ?_ hpr0.le
    rw [convolveKernel_commuted]
    simpa only [enorm_smul, mul_comm] using
      enorm_integral_le_lintegral_enorm (fun y => f (x - y) • K y)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hconv,
    eLpNorm_one_eq_lintegral_enorm hK.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hf.aestronglyMeasurable]
  have hb := ENNReal.rpow_le_rpow he (show 0 ≤ 1 / p.toReal by positivity)
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ (show 0 ≤ 1 / p.toReal by positivity),
    ← ENNReal.rpow_mul, mul_one_div_cancel hpr0.ne', ENNReal.rpow_one] using hb

end OAI.Analysis.Fourier.SquareFunction

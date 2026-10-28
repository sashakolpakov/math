import OAI.Analysis.Fourier.BochnerRiesz.SchwartzKernel
import OAI.Analysis.Fourier.BochnerRiesz.LittlewoodPaleyNorm

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform
open scoped ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem exists_schwartz_angularInverse {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ∃ K : SchwartzMap (Space n) ℂ, (K : Space n → ℂ) = OAI.Analysis.Fourier.LocalSmoothing.angularInverse χ := by
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  let g : SchwartzMap (Space n) ℂ := schwartzDilate (2 * Real.pi) hp (hc.toSchwartzMap hχ)
  refine ⟨𝓕⁻ g, ?_⟩
  funext x
  rw [OAI.Analysis.Fourier.Wave.angularInverse_eq_fourierInv_scaled, SchwartzMap.fourierInv_coe]
  rfl

theorem angularInverse_kernel_decay {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (q : ℝ) :
    ∃ C : ℝ, 0 < C ∧ Differentiable ℝ (OAI.Analysis.Fourier.LocalSmoothing.angularInverse χ) ∧ ∀ x : Space n,
      ‖OAI.Analysis.Fourier.LocalSmoothing.angularInverse χ x‖ ≤ C * (‖x‖ + 1) ^ (-q) ∧
      ‖fderiv ℝ (OAI.Analysis.Fourier.LocalSmoothing.angularInverse χ) x‖ ≤ C * (‖x‖ + 1) ^ (-q) := by
  obtain ⟨K, hK⟩ := exists_schwartz_angularInverse hχ hc
  obtain ⟨C, hC, hb⟩ := schwartz_kernel_decay K q
  refine ⟨C, hC, ?_, ?_⟩
  · rw [← hK]
    exact K.differentiable
  · simpa only [hK] using hb

theorem dyadicAnnularKernel_eq_dilatedKernel {n : ℕ} (χ : Space n → ℂ) (k : ℤ) :
    dyadicAnnularKernel χ k = OAI.Analysis.Fourier.SquareFunction.dilatedKernel (OAI.Analysis.Fourier.LocalSmoothing.angularInverse χ) ((2 : ℝ) ^ k) := by
  funext x
  have h := angularInverse_dilate χ (r := (2 : ℝ) ^ (-k)) (zpow_pos (by norm_num) _) x
  simpa only [dyadicAnnularKernel, OAI.Analysis.Fourier.SquareFunction.dilatedKernel, zpow_neg, inv_pow, inv_inv,
    Complex.real_smul, smul_eq_mul] using h

theorem convolveKernel_dyadicAnnularKernel {n : ℕ} (χ f : Space n → ℂ) (k : ℤ) :
    OAI.Analysis.Fourier.SquareFunction.convolveKernel (dyadicAnnularKernel χ k) f = dyadicAnnularConvolution χ k f := by
  funext x
  simp only [OAI.Analysis.Fourier.SquareFunction.convolveKernel, dyadicAnnularConvolution, OAI.Analysis.Fourier.WavePackets.complexConvolution,
    smul_eq_mul]
  have h := integral_sub_left_eq_self
    (fun y : Space n ↦ dyadicAnnularKernel χ k y * f (x - y)) volume x
  simpa only [sub_sub_cancel, mul_comm] using h

end OAI.Analysis.Fourier.BochnerRiesz

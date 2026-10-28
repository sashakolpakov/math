import OAI.Analysis.Fourier.SquareFunction.VectorConvolution
import OAI.Analysis.Fourier.BochnerRiesz.Multiplier
import OAI.Analysis.Fourier.BochnerRiesz.Projection

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform
open scoped ContDiff ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem fourierInv_mul_smooth_eq_convolution {n : ℕ} {a b : Space n → ℂ}
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) (hb : Integrable b) :
    𝓕⁻ (fun ξ ↦ a ξ * b ξ) = OAI.Analysis.Fourier.WavePackets.complexConvolution (𝓕⁻ a) (𝓕⁻ b) volume := by
  let aS : SchwartzMap (Space n) ℂ := hc.toSchwartzMap ha
  let k : SchwartzMap (Space n) ℂ := 𝓕⁻ aS
  have hk : (k : Space n → ℂ) = 𝓕⁻ a := SchwartzMap.fourierInv_coe aS
  have hFk : 𝓕 (k : Space n → ℂ) = a := by
    change (⇑(𝓕 k : SchwartzMap (Space n) ℂ)) = a
    rw [show 𝓕 k = aS from fourier_fourierInv_eq aS]
    rfl
  funext x
  have H := (OAI.Analysis.Fourier.SquareFunction.inverseFourier_smul_eq_convolve hb k.integrable x).2
  rw [hFk] at H
  simpa only [OAI.Analysis.Fourier.SquareFunction.convolveKernel, OAI.Analysis.Fourier.WavePackets.complexConvolution, smul_eq_mul, hk] using H

theorem eLpNorm_fourierInv_mul_smooth_le {n : ℕ} {a b : Space n → ℂ}
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) (hb : Integrable b)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) :
    eLpNorm (𝓕⁻ (fun ξ ↦ a ξ * b ξ)) p volume ≤
      eLpNorm (𝓕⁻ a) 1 volume * eLpNorm (𝓕⁻ b) p volume := by
  rw [fourierInv_mul_smooth_eq_convolution ha hc hb]
  exact OAI.Analysis.Fourier.WavePackets.eLpNorm_complexConvolution_le
    (continuous_fourierInv_of_integrable (ha.continuous.integrable_of_hasCompactSupport hc)).aestronglyMeasurable
    (continuous_fourierInv_of_integrable hb).aestronglyMeasurable hp hpt

theorem eLpNorm_fourierInv_dilated_smooth_factor_le {n : ℕ} {a b : Space n → ℂ}
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) {h : ℝ} (hh : 0 < h)
    (hb : Integrable b) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) :
    eLpNorm (𝓕⁻ (fun ξ ↦ a (h • ((2 * Real.pi) • ξ)) * b ξ)) p volume ≤
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse a) 1 volume * eLpNorm (𝓕⁻ b) p volume := by
  have ham : ContDiff ℝ ∞ (fun ξ : Space n ↦ a (h • ((2 * Real.pi) • ξ))) := by fun_prop
  have hcm : HasCompactSupport (fun ξ : Space n ↦ a (h • ((2 * Real.pi) • ξ))) :=
    (hc.comp_smul hh.ne').comp_smul (by positivity)
  have H := eLpNorm_fourierInv_mul_smooth_le ham hcm hb hp hpt
  have he : (𝓕⁻ (fun ξ : Space n ↦ a (h • ((2 * Real.pi) • ξ)))) =
      OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ a (h • ξ)) := by
    funext x
    rw [OAI.Analysis.Fourier.Wave.angularInverse_eq_fourierInv_scaled]
  rw [he, eLpNorm_angularInverse_dilate_one (ha.continuous.integrable_of_hasCompactSupport hc) hh] at H
  exact H

end OAI.Analysis.Fourier.BochnerRiesz

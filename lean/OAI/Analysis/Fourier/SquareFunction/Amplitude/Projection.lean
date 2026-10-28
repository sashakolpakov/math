import OAI.Analysis.Fourier.SquareFunction.Amplitude.Kernel
import OAI.Analysis.Fourier.SquareFunction.Shell.Projection

open OAI.Analysis.Fourier.Wave

/-! Fixed annular projections are absorbed by every dilation of the
radius-dependent amplitude kernel. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory FourierTransform
open scoped ENNReal ContDiff

theorem amplitudeShellRadiusMap_annularProject {n : ℕ} {A : ℝ × Space n → ℂ}
    (hA : Continuous A) (hcA : HasCompactSupport A) {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hcut : ∀ r ξ, A (r, ξ) ≠ 0 → χ ((2 * Real.pi) • ξ) = 1)
    (φ : SchwartzMap ℝ ℂ) (δ : ℝ) (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    amplitudeShellRadiusMap A hA φ δ (OAI.Analysis.Fourier.BochnerRiesz.annularProject χ 1 f) x =
      amplitudeShellRadiusMap A hA φ δ f x := by
  ext r
  rw [amplitudeShellRadiusMap_apply A hA hcA, amplitudeShellRadiusMap_apply A hA hcA]
  apply congrArg (fun g : Space n → ℂ => 𝓕⁻ g x)
  funext ξ
  simp only [← SchwartzMap.fourier_coe]
  rw [OAI.Analysis.Fourier.BochnerRiesz.fourier_annularProject hχ hcχ (by positivity)]
  simp only [one_smul]
  by_cases hz : A (r, ξ) = 0
  · simp only [hz, zero_mul]
  · rw [hcut r ξ hz, one_mul]

theorem convolve_amplitudeShellKernel_annularProject {n : ℕ} {A : ℝ × Space n → ℂ}
    (hA : Continuous A) (hcA : HasCompactSupport A) {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hcut : ∀ r ξ, A (r, ξ) ≠ 0 → χ ((2 * Real.pi) • ξ) = 1)
    (φ : SchwartzMap ℝ ℂ) (δ : ℝ) (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    convolveKernel (amplitudeShellKernel A hA φ δ) (OAI.Analysis.Fourier.BochnerRiesz.annularProject χ 1 f) x =
      convolveKernel (amplitudeShellKernel A hA φ δ) f x := by
  rw [convolve_amplitudeShellKernel A hA hcA, convolve_amplitudeShellKernel A hA hcA]
  unfold amplitudeShellHilbert
  rw [amplitudeShellRadiusMap_annularProject hA hcA hχ hcχ hcut]

theorem convolve_dilated_amplitudeShellKernel_annularProject {n : ℕ}
    {A : ℝ × Space n → ℂ} (hA : Continuous A) (hcA : HasCompactSupport A)
    {χ : Space n → ℂ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hcut : ∀ r ξ, A (r, ξ) ≠ 0 → χ ((2 * Real.pi) • ξ) = 1)
    (φ : SchwartzMap ℝ ℂ) (δ : ℝ) {a : ℝ} (ha : 0 < a)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    convolveKernel (dilatedKernel (amplitudeShellKernel A hA φ δ) a)
        (OAI.Analysis.Fourier.BochnerRiesz.annularProject χ a⁻¹ f) x =
      convolveKernel (dilatedKernel (amplitudeShellKernel A hA φ δ) a) f x := by
  rw [convolve_dilatedKernel _ _ ha, convolve_dilatedKernel _ _ ha]
  change convolveKernel (amplitudeShellKernel A hA φ δ)
      (OAI.Analysis.Fourier.BochnerRiesz.schwartzDilate a⁻¹ (inv_ne_zero ha.ne')
        (OAI.Analysis.Fourier.BochnerRiesz.annularProject χ a⁻¹ f)) (a • x) =
    convolveKernel (amplitudeShellKernel A hA φ δ)
      (OAI.Analysis.Fourier.BochnerRiesz.schwartzDilate a⁻¹ (inv_ne_zero ha.ne') f) (a • x)
  have hd := OAI.Analysis.Fourier.BochnerRiesz.annularProject_schwartzDilate hχ hcχ
    (h := 1) (by positivity) (inv_pos.mpr ha) f
  simp only [one_mul] at hd
  rw [← hd]
  exact convolve_amplitudeShellKernel_annularProject hA hcA hχ hcχ hcut φ δ _ _

end OAI.Analysis.Fourier.SquareFunction

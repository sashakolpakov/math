import OAI.Analysis.Fourier.SquareFunction.Shell.OperatorBounds
import OAI.Analysis.Fourier.SquareFunction.CombiningDilates
import OAI.Analysis.Fourier.BochnerRiesz.ProjectionDilation

open OAI.Analysis.Fourier.Wave

/-! Exact insertion of the annular Littlewood--Paley projections into
every normalized dilation of the shell kernel. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory FourierTransform
open scoped ContDiff ENNReal

theorem annularProject_absorb {n : ℕ} {χ ψ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hcut : ∀ ξ, χ ξ ≠ 0 → ψ ξ = 1) (f : SchwartzMap (Space n) ℂ) :
    OAI.Analysis.Fourier.BochnerRiesz.annularProject χ 1 (OAI.Analysis.Fourier.BochnerRiesz.annularProject ψ 1 f) =
      OAI.Analysis.Fourier.BochnerRiesz.annularProject χ 1 f := by
  have hF : 𝓕 (OAI.Analysis.Fourier.BochnerRiesz.annularProject χ 1 (OAI.Analysis.Fourier.BochnerRiesz.annularProject ψ 1 f)) =
      𝓕 (OAI.Analysis.Fourier.BochnerRiesz.annularProject χ 1 f) := by
    ext ξ
    rw [OAI.Analysis.Fourier.BochnerRiesz.fourier_annularProject hχ hcχ (by positivity),
      OAI.Analysis.Fourier.BochnerRiesz.fourier_annularProject hχ hcχ (by positivity),
      OAI.Analysis.Fourier.BochnerRiesz.fourier_annularProject hψ hcψ (by positivity)]
    simp only [one_smul]
    by_cases hz : χ ((2 * Real.pi) • ξ) = 0
    · simp only [hz, zero_mul]
    · rw [hcut _ hz, one_mul]
  simpa only [fourierInv_fourier_eq] using
    congrArg (fun g : SchwartzMap (Space n) ℂ => 𝓕⁻ g) hF

theorem convolve_thinShellKernel_annularProject {n : ℕ} {χ ψ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hcut : ∀ ξ, χ ξ ≠ 0 → ψ ξ = 1)
    (φ : SchwartzMap ℝ ℂ) (δ : ℝ) (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    convolveKernel (thinShellKernel χ hχ.continuous φ δ)
        (OAI.Analysis.Fourier.BochnerRiesz.annularProject ψ 1 f) x =
      convolveKernel (thinShellKernel χ hχ.continuous φ δ) f x := by
  rw [convolve_thinShellKernel hχ hcχ, convolve_thinShellKernel hχ hcχ,
    annularProject_absorb hχ hcχ hψ hcψ hcut]

theorem convolve_dilated_thinShellKernel_annularProject {n : ℕ} {χ ψ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hcut : ∀ ξ, χ ξ ≠ 0 → ψ ξ = 1)
    (φ : SchwartzMap ℝ ℂ) (δ : ℝ) {a : ℝ} (ha : 0 < a)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    convolveKernel (dilatedKernel (thinShellKernel χ hχ.continuous φ δ) a)
        (OAI.Analysis.Fourier.BochnerRiesz.annularProject ψ a⁻¹ f) x =
      convolveKernel (dilatedKernel (thinShellKernel χ hχ.continuous φ δ) a) f x := by
  rw [convolve_dilatedKernel _ _ ha, convolve_dilatedKernel _ _ ha]
  change convolveKernel (thinShellKernel χ hχ.continuous φ δ)
      (OAI.Analysis.Fourier.BochnerRiesz.schwartzDilate a⁻¹ (inv_ne_zero ha.ne')
        (OAI.Analysis.Fourier.BochnerRiesz.annularProject ψ a⁻¹ f)) (a • x) =
    convolveKernel (thinShellKernel χ hχ.continuous φ δ)
      (OAI.Analysis.Fourier.BochnerRiesz.schwartzDilate a⁻¹ (inv_ne_zero ha.ne') f) (a • x)
  have hd := OAI.Analysis.Fourier.BochnerRiesz.annularProject_schwartzDilate hψ hcψ
    (h := 1) (by positivity) (inv_pos.mpr ha) f
  simp only [one_mul] at hd
  rw [← hd]
  exact convolve_thinShellKernel_annularProject hχ hcχ hψ hcψ hcut φ δ _ _

end OAI.Analysis.Fourier.SquareFunction

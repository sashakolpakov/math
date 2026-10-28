import OAI.Analysis.Fourier.BochnerRiesz.AnnularKernel

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform
open scoped ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem exists_schwartz_angularInverse_pair {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ∃ u : SchwartzMap (Space n) ℂ, (u : Space n → ℂ) = OAI.Analysis.Fourier.LocalSmoothing.angularInverse χ ∧
      ∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier u ξ = χ ξ := by
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  let g : SchwartzMap (Space n) ℂ := OAI.Analysis.Fourier.BochnerRiesz.schwartzDilate (2 * Real.pi) hp (hc.toSchwartzMap hχ)
  refine ⟨𝓕⁻ g, ?_, ?_⟩
  · funext x
    rw [OAI.Analysis.Fourier.Wave.angularInverse_eq_fourierInv_scaled, SchwartzMap.fourierInv_coe]
    rfl
  · intro ξ
    have he : (2 * Real.pi) • ((2 * Real.pi)⁻¹ • ξ) = ξ := by
      rw [smul_smul, mul_inv_cancel₀ hp, one_smul]
    conv_lhs => rw [← he]
    rw [OAI.Analysis.Fourier.Wave.angularFourier_scaled]
    change (𝓕 (𝓕⁻ g) : SchwartzMap (Space n) ℂ) ((2 * Real.pi)⁻¹ • ξ) = _
    rw [FourierTransform.fourier_fourierInv_eq]
    change χ ((2 * Real.pi) • ((2 * Real.pi)⁻¹ • ξ)) = χ ξ
    rw [he]

end OAI.Analysis.Fourier.Restriction

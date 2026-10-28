import OAI.Analysis.Fourier.BochnerRiesz.MaximalShell
import OAI.Analysis.Fourier.BochnerRiesz.FiniteFourier
import OAI.Analysis.Fourier.BochnerRiesz.SmoothFactor

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem integrable_dilatedShellSymbol {n : ℕ} (φ : SchwartzMap ℝ ℂ) (Λ ρ : ℝ)
    (f : SchwartzMap (Space n) ℂ) :
    Integrable (fun ξ : Space n ↦ φ (Λ - ρ * ‖ξ‖) * (𝓕 f : SchwartzMap (Space n) ℂ) ξ) := by
  apply integrable_mul_of_bounded_left
    (show AEStronglyMeasurable (fun ξ : Space n ↦ φ (Λ - ρ * ‖ξ‖)) (volume : Measure (Space n)) from
      (φ.continuous.comp (continuous_const.sub (continuous_const.mul continuous_norm))).aestronglyMeasurable)
    (show 0 ≤ SchwartzMap.seminorm ℝ 0 0 φ from by positivity)
    (fun ξ ↦ SchwartzMap.norm_le_seminorm ℝ φ _)
    (𝓕 f).integrable

theorem continuous_dilatedShellCycles {n : ℕ} (φ : SchwartzMap ℝ ℂ) (Λ ρ : ℝ)
    (f : SchwartzMap (Space n) ℂ) : Continuous (dilatedShellCycles φ Λ ρ f) :=
  continuous_fourierInv_of_integrable (integrable_dilatedShellSymbol φ Λ ρ f)

theorem eLpNorm_dilatedShellCycles_le_maximal {n : ℕ} (φ : SchwartzMap ℝ ℂ) (Λ : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (f : SchwartzMap (Space n) ℂ) (p : ℝ≥0∞) :
    eLpNorm (dilatedShellCycles φ Λ ρ f) p volume ≤
      eLpNorm (maximalShellCycles φ Λ f) p volume := by
  apply eLpNorm_mono_enorm (continuous_dilatedShellCycles φ Λ ρ f).aestronglyMeasurable
  intro x
  rw [enorm_eq_self]
  exact le_iSup_of_le ⟨ρ, hρ⟩ le_rfl

theorem eLpNorm_smooth_dilatedShell_le {n : ℕ} {a : Space n → ℂ}
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) (φ : SchwartzMap ℝ ℂ) (Λ : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (f : SchwartzMap (Space n) ℂ) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpt : p ≠ ⊤) :
    eLpNorm (𝓕⁻ (fun ξ : Space n ↦ a ((2 * Real.pi) • ξ) *
      (φ (Λ - ρ * ‖ξ‖) * (𝓕 f : SchwartzMap (Space n) ℂ) ξ))) p volume ≤
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse a) 1 volume * eLpNorm (maximalShellCycles φ Λ f) p volume := by
  have H := eLpNorm_fourierInv_dilated_smooth_factor_le ha hc (show (0 : ℝ) < 1 by norm_num)
    (integrable_dilatedShellSymbol φ Λ ρ f) hp hpt
  simp only [one_smul] at H
  exact H.trans (mul_le_mul' le_rfl (eLpNorm_dilatedShellCycles_le_maximal φ Λ hρ f p))

end OAI.Analysis.Fourier.BochnerRiesz

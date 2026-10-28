import OAI.Analysis.Fourier.SquareFunction.Shell.L2
import OAI.Analysis.Fourier.BochnerRiesz.MultiplierCompatibility

open OAI.Analysis.Fourier.Wave

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory FourierTransform
open scoped ENNReal

theorem eLpNorm_fourier_cycles {n : ℕ} {g : Space n → ℂ}
    (hg : Integrable g) (hg₂ : MemLp g 2) :
    eLpNorm (𝓕 g) 2 volume = eLpNorm g 2 volume := by
  let g₂ : OAI.Analysis.Fourier.Wave.WaveL2 n := hg₂.toLp g
  have hcoe : (g₂ : Space n → ℂ) =ᵐ[volume] g := hg₂.coeFn_toLp
  have hfg : (fun x => ((Lp.fourierTransformₗᵢ (Space n) ℂ) g₂) x) =ᵐ[volume] 𝓕 g :=
    OAI.Analysis.Fourier.BochnerRiesz.fourier_toLp_ae hg hg₂
  rw [← eLpNorm_congr_ae hfg, ← Lp.enorm_def, ← ofReal_norm,
    LinearIsometryEquiv.norm_map, ofReal_norm, Lp.enorm_def, eLpNorm_congr_ae hcoe]

theorem eLpNorm_fourierInv_cycles {n : ℕ} {g : Space n → ℂ}
    (hg : Integrable g) (hg₂ : MemLp g 2) :
    eLpNorm (𝓕⁻ g) 2 volume = eLpNorm g 2 volume := by
  let g₂ : OAI.Analysis.Fourier.Wave.WaveL2 n := hg₂.toLp g
  have hcoe : (g₂ : Space n → ℂ) =ᵐ[volume] g := hg₂.coeFn_toLp
  have hfg : (fun x => ((Lp.fourierTransformₗᵢ (Space n) ℂ).symm g₂) x) =ᵐ[volume] 𝓕⁻ g := by
    filter_upwards [OAI.Analysis.Fourier.Wave.inverseFourierL2_coe g₂ (hg.congr hcoe.symm)] with x hx
    exact hx.trans (Real.fourierInv_congr_ae hcoe x)
  rw [← eLpNorm_congr_ae hfg, ← Lp.enorm_def, ← ofReal_norm,
    LinearIsometryEquiv.norm_map, ofReal_norm, Lp.enorm_def, eLpNorm_congr_ae hcoe]

theorem lintegral_fourierInv_cycles {n : ℕ} {g : Space n → ℂ}
    (hg : Integrable g) (hg₂ : MemLp g 2) :
    (∫⁻ x, ‖𝓕⁻ g x‖ₑ ^ (2 : ℝ)) = ∫⁻ ξ, ‖g ξ‖ₑ ^ (2 : ℝ) := by
  have hc : Continuous (𝓕⁻ g) := OAI.Analysis.Fourier.BochnerRiesz.continuous_fourierInv_of_integrable hg
  rw [← eLpNorm_two_rpow_general volume hc.aestronglyMeasurable,
    eLpNorm_fourierInv_cycles hg hg₂,
    eLpNorm_two_rpow_general volume hg.aestronglyMeasurable]

end OAI.Analysis.Fourier.SquareFunction

import OAI.Analysis.Fourier.BochnerRiesz.OperatorPartition

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem schwartz_fourierInv_apply_eq_fourier_neg {n : ℕ}
    (f : SchwartzMap (Space n) ℂ) (ξ : Space n) : (𝓕⁻ f) ξ = (𝓕 f) (-ξ) := by
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg]
  exact congrFun (SchwartzMap.fourier_coe f).symm (-ξ)

theorem even_multiplier_integral_pairing {n : ℕ} {m : Space n → ℂ}
    (heven : ∀ ξ, m (-ξ) = m ξ) (f g : SchwartzMap (Space n) ℂ)
    (hf : Integrable (fun ξ ↦ m ξ * (𝓕 f : SchwartzMap (Space n) ℂ) ξ))
    (hg : Integrable (fun ξ ↦ m ξ * (𝓕 g : SchwartzMap (Space n) ℂ) ξ)) :
    (∫ x, g x * 𝓕⁻ (fun ξ ↦ m ξ * (𝓕 f : SchwartzMap (Space n) ℂ) ξ) x) =
      ∫ x, f x * 𝓕⁻ (fun ξ ↦ m ξ * (𝓕 g : SchwartzMap (Space n) ℂ) ξ) x := by
  rw [← OAI.Analysis.Fourier.Wave.inverseFourier_integral_pairing _ hf g, ← OAI.Analysis.Fourier.Wave.inverseFourier_integral_pairing _ hg f]
  rw [← integral_neg_eq_self (fun ξ : Space n ↦ (𝓕⁻ g : SchwartzMap (Space n) ℂ) ξ *
    (m ξ * (𝓕 f : SchwartzMap (Space n) ℂ) ξ)) volume]
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [heven, schwartz_fourierInv_apply_eq_fourier_neg, neg_neg,
    schwartz_fourierInv_apply_eq_fourier_neg]
  ring

theorem even_brInteriorSymbol {n : ℕ} (δ : ℝ) (J : ℕ) (ξ : Space n) :
    brInteriorSymbol δ J (-ξ) = brInteriorSymbol δ J ξ := by
  simp only [brInteriorSymbol, brInteriorReal, OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol, norm_neg]

theorem brInteriorCycles_integral_pairing {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {J : ℕ} (hJ : 2 ≤ J) (f g : SchwartzMap (Space n) ℂ) :
    (∫ x, g x * brInteriorCycles δ J f x) = ∫ x, f x * brInteriorCycles δ J g x := by
  apply even_multiplier_integral_pairing
    (fun ξ ↦ by rw [smul_neg, even_brInteriorSymbol]) f g
  · exact integrable_smooth_cycles_mul (contDiff_brInteriorSymbol hδ hJ)
      (hasCompactSupport_brInteriorSymbol hδ J) (𝓕 f).integrable
  · exact integrable_smooth_cycles_mul (contDiff_brInteriorSymbol hδ hJ)
      (hasCompactSupport_brInteriorSymbol hδ J) (𝓕 g).integrable

end OAI.Analysis.Fourier.BochnerRiesz

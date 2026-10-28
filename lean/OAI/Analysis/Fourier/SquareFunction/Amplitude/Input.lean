import OAI.Analysis.Fourier.WavePackets.PartialFourierSmooth
import OAI.Analysis.Fourier.SquareFunction.VectorYoung
import OAI.Analysis.Fourier.SquareFunction.VectorConvolution
import Mathlib.Analysis.Distribution.FourierMultiplier

open OAI.Analysis.Fourier.Wave

/-! The separated amplitude acts on the spatial input by an integrable
Fourier multiplier, with a summable bound in the separation parameter. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory FourierTransform
open scoped ENNReal ContDiff

noncomputable def amplitudeInput {n : ℕ} (A : ℝ × Space n → ℂ)
    (η : ℝ) (f : SchwartzMap (Space n) ℂ) : SchwartzMap (Space n) ℂ :=
  SchwartzMap.fourierMultiplierCLM ℂ (OAI.Analysis.Fourier.WavePackets.partialRadiusFourier A η) f

theorem amplitudeInput_symbol_temperate {n : ℕ} {A : ℝ × Space n → ℂ}
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A) (η : ℝ) :
    Function.HasTemperateGrowth (OAI.Analysis.Fourier.WavePackets.partialRadiusFourier A η) :=
  (OAI.Analysis.Fourier.WavePackets.hasCompactSupport_partialRadiusFourier hc η).hasTemperateGrowth
    (OAI.Analysis.Fourier.WavePackets.contDiff_partialRadiusFourier hA hc η)

theorem fourier_amplitudeInput {n : ℕ} {A : ℝ × Space n → ℂ}
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A) (η : ℝ)
    (f : SchwartzMap (Space n) ℂ) (ξ : Space n) :
    (𝓕 (amplitudeInput A η f) : SchwartzMap (Space n) ℂ) ξ =
      OAI.Analysis.Fourier.WavePackets.partialRadiusFourier A η ξ * (𝓕 f : SchwartzMap (Space n) ℂ) ξ := by
  rw [amplitudeInput, SchwartzMap.fourierMultiplierCLM_apply, fourier_fourierInv_eq,
    SchwartzMap.smulLeftCLM_apply_apply (amplitudeInput_symbol_temperate hA hc η)]
  rfl

theorem amplitudeInput_eq_convolve {n : ℕ} {A : ℝ × Space n → ℂ}
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A) (η : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    amplitudeInput A η f x =
      convolveKernel (𝓕⁻ (OAI.Analysis.Fourier.WavePackets.partialRadiusFourier A η)) f x := by
  have hi : Integrable (OAI.Analysis.Fourier.WavePackets.partialRadiusFourier A η) :=
    (OAI.Analysis.Fourier.WavePackets.contDiff_partialRadiusFourier hA hc η).continuous.integrable_of_hasCompactSupport
      (OAI.Analysis.Fourier.WavePackets.hasCompactSupport_partialRadiusFourier hc η)
  rw [amplitudeInput, SchwartzMap.fourierMultiplierCLM_apply, SchwartzMap.fourierInv_coe]
  have he : (SchwartzMap.smulLeftCLM ℂ (OAI.Analysis.Fourier.WavePackets.partialRadiusFourier A η) (𝓕 f) : Space n → ℂ) =
      fun ξ => 𝓕 (f : Space n → ℂ) ξ • OAI.Analysis.Fourier.WavePackets.partialRadiusFourier A η ξ := by
    funext ξ
    rw [SchwartzMap.smulLeftCLM_apply_apply (amplitudeInput_symbol_temperate hA hc η)]
    simp only [smul_eq_mul, SchwartzMap.fourier_coe, mul_comm]
  rw [he]
  exact (inverseFourier_smul_eq_convolve hi f.integrable x).2

theorem norm_compact_symbol_le_inverse_L1 {n : ℕ} {m : Space n → ℂ}
    (hm : ContDiff ℝ ∞ m) (hc : HasCompactSupport m) (ξ : Space n) :
    ‖m ξ‖ ≤ ∫ x, ‖𝓕⁻ m x‖ := by
  let g : SchwartzMap (Space n) ℂ := hc.toSchwartzMap hm
  have he : 𝓕 (𝓕⁻ m) = m := by
    change 𝓕 (𝓕⁻ (g : Space n → ℂ)) = (g : Space n → ℂ)
    rw [← SchwartzMap.fourierInv_coe, ← SchwartzMap.fourier_coe, fourier_fourierInv_eq]
  calc
    ‖m ξ‖ = ‖𝓕 (𝓕⁻ m) ξ‖ := congrArg norm (congrFun he ξ).symm
    _ ≤ _ := VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
      (innerₗ (Space n)) (𝓕⁻ m) ξ

theorem amplitudeInput_bound {n : ℕ} {A : ℝ × Space n → ℂ}
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : ℝ,
      (∀ ξ, ‖OAI.Analysis.Fourier.WavePackets.partialRadiusFourier A η ξ‖ ≤ C * (1 + |η|) ^ (-2 : ℝ)) ∧
      ∀ (f : SchwartzMap (Space n) ℂ) (p : ℝ≥0∞), 1 ≤ p → p ≠ ⊤ →
        eLpNorm (amplitudeInput A η f) p volume ≤
          ENNReal.ofReal (C * (1 + |η|) ^ (-2 : ℝ)) * eLpNorm f p volume := by
  obtain ⟨C, hC, hb⟩ := OAI.Analysis.Fourier.WavePackets.partialRadiusFourier_inverse_L1 hA hc
  refine ⟨C, hC, ?_⟩
  intro η
  have hm := OAI.Analysis.Fourier.WavePackets.contDiff_partialRadiusFourier hA hc η
  have hcm := OAI.Analysis.Fourier.WavePackets.hasCompactSupport_partialRadiusFourier hc η
  constructor
  · intro ξ
    exact (norm_compact_symbol_le_inverse_L1 hm hcm ξ).trans (hb η).2
  intro f p hp hpt
  have hK : Continuous (𝓕⁻ (OAI.Analysis.Fourier.WavePackets.partialRadiusFourier A η)) :=
    (differentiable_fourierInv_compact hm.continuous hcm).continuous
  have he : (amplitudeInput A η f : Space n → ℂ) =
      convolveKernel (𝓕⁻ (OAI.Analysis.Fourier.WavePackets.partialRadiusFourier A η)) f :=
    funext (amplitudeInput_eq_convolve hA hc η f)
  rw [he]
  apply (eLpNorm_convolveKernel_le hK f.continuous.measurable hp hpt).trans
  apply mul_le_mul' ?_ le_rfl
  rw [eLpNorm_one_eq_lintegral_enorm hK.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm (hb η).1]
  exact ENNReal.ofReal_le_ofReal (hb η).2

theorem partialRadiusFourier_cutoff {n : ℕ} {A : ℝ × Space n → ℂ}
    {χ : Space n → ℂ} (hcut : ∀ r ξ, A (r, ξ) ≠ 0 → χ ((2 * Real.pi) • ξ) = 1)
    (η : ℝ) (ξ : Space n) (ha : OAI.Analysis.Fourier.WavePackets.partialRadiusFourier A η ξ ≠ 0) :
    χ ((2 * Real.pi) • ξ) = 1 := by
  by_contra hn
  have hz : (fun r : ℝ => A (r, ξ)) = 0 := by
    funext r
    by_contra hr
    exact hn (hcut r ξ hr)
  apply ha
  simp [OAI.Analysis.Fourier.WavePackets.partialRadiusFourier, hz, Real.fourier_eq]

theorem annularProject_amplitudeInput {n : ℕ} {A : ℝ × Space n → ℂ}
    (hA : ContDiff ℝ ∞ A) (hcA : HasCompactSupport A) {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hcut : ∀ r ξ, A (r, ξ) ≠ 0 → χ ((2 * Real.pi) • ξ) = 1)
    (η : ℝ) (f : SchwartzMap (Space n) ℂ) :
    OAI.Analysis.Fourier.BochnerRiesz.annularProject χ 1 (amplitudeInput A η f) = amplitudeInput A η f := by
  have he : (𝓕 (OAI.Analysis.Fourier.BochnerRiesz.annularProject χ 1 (amplitudeInput A η f)) :
      SchwartzMap (Space n) ℂ) = 𝓕 (amplitudeInput A η f) := by
    ext ξ
    rw [OAI.Analysis.Fourier.BochnerRiesz.fourier_annularProject hχ hcχ (by positivity), one_smul,
      fourier_amplitudeInput hA hcA]
    by_cases hz : OAI.Analysis.Fourier.WavePackets.partialRadiusFourier A η ξ = 0
    · simp only [hz, zero_mul, mul_zero]
    · rw [partialRadiusFourier_cutoff hcut η ξ hz, one_mul]
  calc
    _ = (𝓕⁻ (𝓕 (OAI.Analysis.Fourier.BochnerRiesz.annularProject χ 1 (amplitudeInput A η f)) :
        SchwartzMap (Space n) ℂ) : SchwartzMap (Space n) ℂ) :=
      (fourierInv_fourier_eq _).symm
    _ = _ := by rw [he, fourierInv_fourier_eq]

end OAI.Analysis.Fourier.SquareFunction

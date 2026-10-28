import OAI.Analysis.Fourier.SquareFunction.Amplitude.Kernel
import OAI.Analysis.Fourier.BochnerRiesz.MultiplierCompatibility

open OAI.Analysis.Fourier.Wave

/-! Compact smooth radius-dependent Fourier symbols, without any annular
support assumption. This includes the low-frequency Stein remainder. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory FourierTransform Set

noncomputable def smoothRadiusSymbol {n : ℕ} (A : ℝ × Space n → ℂ)
    (hA : Continuous A) : Space n → C(RadiusInterval, ℂ) :=
  radiusCurry (fun z => A (z.2, z.1)) (hA.comp continuous_swap)

@[simp] theorem smoothRadiusSymbol_apply {n : ℕ} (A : ℝ × Space n → ℂ)
    (hA : Continuous A) (ξ : Space n) (r : RadiusInterval) :
    smoothRadiusSymbol A hA ξ r = A (r, ξ) := rfl

theorem continuous_smoothRadiusSymbol {n : ℕ} (A : ℝ × Space n → ℂ)
    (hA : Continuous A) : Continuous (smoothRadiusSymbol A hA) :=
  continuous_radiusCurry _ _

theorem hasCompactSupport_smoothRadiusSymbol {n : ℕ} (A : ℝ × Space n → ℂ)
    (hA : Continuous A) (hc : HasCompactSupport A) :
    HasCompactSupport (smoothRadiusSymbol A hA) := by
  apply HasCompactSupport.of_support_subset_isCompact (hc.image continuous_snd)
  intro ξ hξ
  by_contra hnot
  apply hξ
  ext r
  have hz : A (r, ξ) = 0 := by
    by_contra hn
    exact hnot ⟨(r, ξ), subset_tsupport A hn, rfl⟩
  simp only [smoothRadiusSymbol_apply, hz, ContinuousMap.zero_apply]

noncomputable def smoothRadiusKernel {n : ℕ} (A : ℝ × Space n → ℂ)
    (hA : Continuous A) : Space n → RadiusHilbert :=
  radiusFourierKernel (smoothRadiusSymbol A hA)

theorem differentiable_smoothRadiusKernel {n : ℕ} (A : ℝ × Space n → ℂ)
    (hA : Continuous A) (hc : HasCompactSupport A) :
    Differentiable ℝ (smoothRadiusKernel A hA) :=
  differentiable_radiusFourierKernel (continuous_smoothRadiusSymbol A hA)
    (hasCompactSupport_smoothRadiusSymbol A hA hc)

noncomputable def smoothRadiusOutput {n : ℕ} (A : ℝ × Space n → ℂ)
    (hA : Continuous A) (f : Space n → ℂ) (x : Space n) : C(RadiusInterval, ℂ) :=
  𝓕⁻ (fun ξ => 𝓕 f ξ • smoothRadiusSymbol A hA ξ) x

theorem smoothRadiusOutput_apply {n : ℕ} (A : ℝ × Space n → ℂ)
    (hA : Continuous A) (hc : HasCompactSupport A) {f : Space n → ℂ}
    (hf : Integrable f) (x : Space n) (r : RadiusInterval) :
    smoothRadiusOutput A hA f x r =
      𝓕⁻ (fun ξ => A (r, ξ) * 𝓕 f ξ) x := by
  have hi : Integrable (fun ξ => 𝓕 f ξ • smoothRadiusSymbol A hA ξ) :=
    integrable_continuous_smul_compact (OAI.Analysis.Fourier.BochnerRiesz.continuous_fourier_of_integrable hf)
      (continuous_smoothRadiusSymbol A hA) (hasCompactSupport_smoothRadiusSymbol A hA hc)
  unfold smoothRadiusOutput
  rw [fourierInv_continuousMap_apply hi]
  apply congrArg (fun g : Space n → ℂ => 𝓕⁻ g x)
  funext ξ
  simp only [ContinuousMap.smul_apply, smul_eq_mul, smoothRadiusSymbol_apply, mul_comm]

theorem convolve_smoothRadiusKernel {n : ℕ} (A : ℝ × Space n → ℂ)
    (hA : Continuous A) (hc : HasCompactSupport A) {f : Space n → ℂ}
    (hf : Integrable f) (x : Space n) :
    convolveKernel (smoothRadiusKernel A hA) f x =
      radiusToL2 (smoothRadiusOutput A hA f x) :=
  convolve_radiusFourierKernel
    ((continuous_smoothRadiusSymbol A hA).integrable_of_hasCompactSupport
      (hasCompactSupport_smoothRadiusSymbol A hA hc)) hf x

theorem smoothRadiusKernel_coe {n : ℕ} (A : ℝ × Space n → ℂ)
    (hA : Continuous A) (hc : HasCompactSupport A) (x : Space n) :
    (smoothRadiusKernel A hA x : RadiusInterval → ℂ) =ᵐ[radiusMeasure]
      (fun r => 𝓕⁻ (fun ξ : Space n => A (r, ξ)) x) :=
  radiusFourierKernel_coe
    ((continuous_smoothRadiusSymbol A hA).integrable_of_hasCompactSupport
      (hasCompactSupport_smoothRadiusSymbol A hA hc)) x

end OAI.Analysis.Fourier.SquareFunction

import OAI.Analysis.Fourier.SquareFunction.Shell.Kernel
import OAI.Analysis.Fourier.SquareFunction.Shell.Convolution
import OAI.Analysis.Fourier.WavePackets.PartialFourier

open OAI.Analysis.Fourier.Wave

/-! Radius-dependent compact amplitudes in the thin-shell operator. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory FourierTransform Set

theorem continuous_amplitude_shell_symbol {n : ℕ} {A : ℝ × Space n → ℂ}
    (hA : Continuous A) (φ : SchwartzMap ℝ ℂ) (δ : ℝ) :
    Continuous (fun z : Space n × ℝ =>
      A (z.2, z.1) * φ ((z.2 - ‖z.1‖) / δ)) := by
  have hφ := φ.continuous
  fun_prop

noncomputable def amplitudeShellSymbol {n : ℕ} (A : ℝ × Space n → ℂ)
    (hA : Continuous A) (φ : SchwartzMap ℝ ℂ) (δ : ℝ) :
    Space n → C(RadiusInterval, ℂ) :=
  radiusCurry (fun z => A (z.2, z.1) * φ ((z.2 - ‖z.1‖) / δ))
    (continuous_amplitude_shell_symbol hA φ δ)

@[simp] theorem amplitudeShellSymbol_apply {n : ℕ} (A : ℝ × Space n → ℂ)
    (hA : Continuous A) (φ : SchwartzMap ℝ ℂ) (δ : ℝ)
    (ξ : Space n) (r : RadiusInterval) :
    amplitudeShellSymbol A hA φ δ ξ r =
      A (r, ξ) * φ (((r : ℝ) - ‖ξ‖) / δ) := rfl

theorem continuous_amplitudeShellSymbol {n : ℕ} (A : ℝ × Space n → ℂ)
    (hA : Continuous A) (φ : SchwartzMap ℝ ℂ) (δ : ℝ) :
    Continuous (amplitudeShellSymbol A hA φ δ) := continuous_radiusCurry _ _

theorem hasCompactSupport_amplitudeShellSymbol {n : ℕ} (A : ℝ × Space n → ℂ)
    (hA : Continuous A) (hc : HasCompactSupport A) (φ : SchwartzMap ℝ ℂ) (δ : ℝ) :
    HasCompactSupport (amplitudeShellSymbol A hA φ δ) := by
  apply HasCompactSupport.of_support_subset_isCompact (hc.image continuous_snd)
  intro ξ hξ
  by_contra hnot
  apply hξ
  ext r
  have hz : A (r, ξ) = 0 := by
    by_contra hn
    exact hnot ⟨(r, ξ), subset_tsupport A hn, rfl⟩
  simp only [amplitudeShellSymbol_apply, hz, zero_mul, ContinuousMap.zero_apply]

noncomputable def amplitudeShellKernel {n : ℕ} (A : ℝ × Space n → ℂ)
    (hA : Continuous A) (φ : SchwartzMap ℝ ℂ) (δ : ℝ) : Space n → RadiusHilbert :=
  radiusFourierKernel (amplitudeShellSymbol A hA φ δ)

theorem differentiable_amplitudeShellKernel {n : ℕ} (A : ℝ × Space n → ℂ)
    (hA : Continuous A) (hc : HasCompactSupport A) (φ : SchwartzMap ℝ ℂ) (δ : ℝ) :
    Differentiable ℝ (amplitudeShellKernel A hA φ δ) :=
  differentiable_radiusFourierKernel (continuous_amplitudeShellSymbol A hA φ δ)
    (hasCompactSupport_amplitudeShellSymbol A hA hc φ δ)

theorem amplitudeShellKernel_coe {n : ℕ} (A : ℝ × Space n → ℂ)
    (hA : Continuous A) (hc : HasCompactSupport A) (φ : SchwartzMap ℝ ℂ) (δ : ℝ)
    (x : Space n) :
    (amplitudeShellKernel A hA φ δ x : RadiusInterval → ℂ) =ᵐ[radiusMeasure]
      (fun r => 𝓕⁻ (fun ξ : Space n =>
        A (r, ξ) * φ (((r : ℝ) - ‖ξ‖) / δ)) x) :=
  radiusFourierKernel_coe ((continuous_amplitudeShellSymbol A hA φ δ).integrable_of_hasCompactSupport
    (hasCompactSupport_amplitudeShellSymbol A hA hc φ δ)) x

noncomputable def amplitudeShellRadiusMap {n : ℕ} (A : ℝ × Space n → ℂ)
    (hA : Continuous A) (φ : SchwartzMap ℝ ℂ) (δ : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) : C(RadiusInterval, ℂ) :=
  𝓕⁻ (fun ξ => 𝓕 (f : Space n → ℂ) ξ • amplitudeShellSymbol A hA φ δ ξ) x

noncomputable def amplitudeShellHilbert {n : ℕ} (A : ℝ × Space n → ℂ)
    (hA : Continuous A) (φ : SchwartzMap ℝ ℂ) (δ : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) : RadiusHilbert :=
  radiusToL2 (amplitudeShellRadiusMap A hA φ δ f x)

theorem amplitudeShellRadiusMap_apply {n : ℕ} (A : ℝ × Space n → ℂ)
    (hA : Continuous A) (hc : HasCompactSupport A) (φ : SchwartzMap ℝ ℂ) (δ : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) (r : RadiusInterval) :
    amplitudeShellRadiusMap A hA φ δ f x r =
      𝓕⁻ (fun ξ => A (r, ξ) * φ (((r : ℝ) - ‖ξ‖) / δ) * 𝓕 (f : Space n → ℂ) ξ) x := by
  have hi : Integrable (fun ξ =>
      𝓕 (f : Space n → ℂ) ξ • amplitudeShellSymbol A hA φ δ ξ) :=
    integrable_continuous_smul_compact (𝓕 f).continuous
      (continuous_amplitudeShellSymbol A hA φ δ)
      (hasCompactSupport_amplitudeShellSymbol A hA hc φ δ)
  unfold amplitudeShellRadiusMap
  rw [fourierInv_continuousMap_apply hi]
  apply congrArg (fun g : Space n → ℂ => 𝓕⁻ g x)
  funext ξ
  simp only [ContinuousMap.smul_apply, smul_eq_mul, amplitudeShellSymbol_apply]
  ring

theorem continuous_amplitudeShellRadiusMap {n : ℕ} (A : ℝ × Space n → ℂ)
    (hA : Continuous A) (hc : HasCompactSupport A) (φ : SchwartzMap ℝ ℂ) (δ : ℝ)
    (f : SchwartzMap (Space n) ℂ) : Continuous (amplitudeShellRadiusMap A hA φ δ f) :=
  (differentiable_fourierInv_compact
    ((𝓕 f).continuous.smul (continuous_amplitudeShellSymbol A hA φ δ))
    (hasCompactSupport_amplitudeShellSymbol A hA hc φ δ).smul_left).continuous

theorem continuous_amplitudeShellHilbert {n : ℕ} (A : ℝ × Space n → ℂ)
    (hA : Continuous A) (hc : HasCompactSupport A) (φ : SchwartzMap ℝ ℂ) (δ : ℝ)
    (f : SchwartzMap (Space n) ℂ) : Continuous (amplitudeShellHilbert A hA φ δ f) :=
  radiusToL2.continuous.comp (continuous_amplitudeShellRadiusMap A hA hc φ δ f)

theorem convolve_amplitudeShellKernel {n : ℕ} (A : ℝ × Space n → ℂ)
    (hA : Continuous A) (hc : HasCompactSupport A) (φ : SchwartzMap ℝ ℂ) (δ : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    convolveKernel (amplitudeShellKernel A hA φ δ) f x =
      amplitudeShellHilbert A hA φ δ f x :=
  convolve_radiusFourierKernel
    ((continuous_amplitudeShellSymbol A hA φ δ).integrable_of_hasCompactSupport
      (hasCompactSupport_amplitudeShellSymbol A hA hc φ δ)) f.integrable x

end OAI.Analysis.Fourier.SquareFunction

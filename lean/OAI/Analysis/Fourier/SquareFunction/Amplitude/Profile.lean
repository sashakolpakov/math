import OAI.Analysis.Fourier.SquareFunction.Amplitude.Dyadic
import OAI.Analysis.Fourier.SquareFunction.FourierDilation

open OAI.Analysis.Fourier.Wave

/-! The actual radius profile represented by the amplitude-shell convolution,
including every spatial dilation. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory FourierTransform Set
open scoped ENNReal ContDiff

noncomputable def amplitudeShellProfile {n : ℕ} (A : ℝ × Space n → ℂ)
    (φ : SchwartzMap ℝ ℂ) (δ a : ℝ) (f : SchwartzMap (Space n) ℂ)
    (x : Space n) (r : ℝ) : ℂ :=
  𝓕⁻ (fun ξ : Space n => A (r, a⁻¹ • ξ) * φ ((r - a⁻¹ * ‖ξ‖) / δ) *
    𝓕 (f : Space n → ℂ) ξ) x

theorem amplitudeShellRadiusMap_dilate {n : ℕ} {A : ℝ × Space n → ℂ}
    (hA : Continuous A) (hcA : HasCompactSupport A)
    (φ : SchwartzMap ℝ ℂ) (δ : ℝ) {a : ℝ} (ha : 0 < a)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) (r : RadiusInterval) :
    amplitudeShellRadiusMap A hA φ δ
        (OAI.Analysis.Fourier.BochnerRiesz.schwartzDilate a⁻¹ (inv_ne_zero ha.ne') f) (a • x) r =
      amplitudeShellProfile A φ δ a f x r := by
  rw [amplitudeShellRadiusMap_apply A hA hcA]
  let m : Space n → ℂ := fun ξ => A (r, ξ) * φ (((r : ℝ) - ‖ξ‖) / δ)
  change 𝓕⁻ (fun ξ => m ξ * 𝓕 (fun y => f (a⁻¹ • y)) ξ) (a • x) = _
  rw [fourierMultiplier_dilate_cycles m f (inv_pos.mpr ha), inv_smul_smul₀ ha.ne']
  unfold amplitudeShellProfile
  apply congrArg (fun b : Space n → ℂ => 𝓕⁻ b x)
  funext ξ
  simp only [m, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]

theorem convolve_dilated_amplitudeShellKernel_hilbert {n : ℕ} {A : ℝ × Space n → ℂ}
    (hA : Continuous A) (hcA : HasCompactSupport A)
    (φ : SchwartzMap ℝ ℂ) (δ : ℝ) {a : ℝ} (ha : 0 < a)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    convolveKernel (dilatedKernel (amplitudeShellKernel A hA φ δ) a) f x =
      amplitudeShellHilbert A hA φ δ
        (OAI.Analysis.Fourier.BochnerRiesz.schwartzDilate a⁻¹ (inv_ne_zero ha.ne') f) (a • x) := by
  rw [convolve_dilatedKernel _ _ ha]
  exact convolve_amplitudeShellKernel A hA hcA φ δ
    (OAI.Analysis.Fourier.BochnerRiesz.schwartzDilate a⁻¹ (inv_ne_zero ha.ne') f) (a • x)

theorem enorm_convolve_dilated_amplitudeShellKernel {n : ℕ} {A : ℝ × Space n → ℂ}
    (hA : Continuous A) (hcA : HasCompactSupport A)
    (φ : SchwartzMap ℝ ℂ) (δ : ℝ) {a : ℝ} (ha : 0 < a)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    ‖convolveKernel (dilatedKernel (amplitudeShellKernel A hA φ δ) a) f x‖ₑ =
      eLpNorm (amplitudeShellProfile A φ δ a f x) 2
        (volume.restrict (Icc (1 : ℝ) 2)) := by
  rw [convolve_dilated_amplitudeShellKernel_hilbert hA hcA φ δ ha f x]
  unfold amplitudeShellHilbert
  rw [enorm_radiusToL2]
  have he := funext (amplitudeShellRadiusMap_dilate hA hcA φ δ ha f x)
  rw [he, eLpNorm_radius_restriction]

theorem dyadicAmplitudeShellSquare_eq_radius_norms {n : ℕ} {A : ℝ × Space n → ℂ}
    (hA : Continuous A) (hcA : HasCompactSupport A)
    (φ : SchwartzMap ℝ ℂ) (δ : ℝ) (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    dyadicAmplitudeShellSquare A hA φ δ f x =
      (∑' k : ℤ, eLpNorm (amplitudeShellProfile A φ δ ((2 : ℝ) ^ k) f x) 2
        (volume.restrict (Icc (1 : ℝ) 2)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  unfold dyadicAmplitudeShellSquare countableSquareNorm dyadicAmplitudeShellHilbert
  congr 1
  apply tsum_congr
  intro k
  rw [enorm_convolve_dilated_amplitudeShellKernel hA hcA φ δ (by positivity)]

theorem continuous_dyadicAmplitudeShellHilbert {n : ℕ} {A : ℝ × Space n → ℂ}
    (hA : Continuous A) (hcA : HasCompactSupport A)
    (φ : SchwartzMap ℝ ℂ) (δ : ℝ) (f : SchwartzMap (Space n) ℂ) (k : ℤ) :
    Continuous (dyadicAmplitudeShellHilbert A hA φ δ f k) := by
  have hk : 0 < (2 : ℝ) ^ k := by positivity
  have he := funext (convolve_dilated_amplitudeShellKernel_hilbert hA hcA φ δ hk f)
  change Continuous (convolveKernel (dilatedKernel (amplitudeShellKernel A hA φ δ) (2 ^ k)) f)
  rw [he]
  exact (continuous_amplitudeShellHilbert A hA hcA φ δ _).comp
    (continuous_id.const_smul ((2 : ℝ) ^ k))

theorem measurable_dyadicAmplitudeShellSquare {n : ℕ} {A : ℝ × Space n → ℂ}
    (hA : Continuous A) (hcA : HasCompactSupport A)
    (φ : SchwartzMap ℝ ℂ) (δ : ℝ) (f : SchwartzMap (Space n) ℂ) :
    Measurable (dyadicAmplitudeShellSquare A hA φ δ f) := by
  let : MeasurableSpace RadiusHilbert := borel RadiusHilbert
  let : BorelSpace RadiusHilbert := ⟨rfl⟩
  unfold dyadicAmplitudeShellSquare countableSquareNorm
  exact (Measurable.tsum (fun k =>
    (continuous_dyadicAmplitudeShellHilbert hA hcA φ δ f k).measurable.enorm.pow_const _)).pow_const _

end OAI.Analysis.Fourier.SquareFunction

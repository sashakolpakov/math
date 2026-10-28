import OAI.Analysis.Fourier.Radial.BRIntegration

open OAI.Analysis.Fourier.Wave

/-! Identification of the radial cosine integral with the exact
angular-normalized Bochner--Riesz convolution kernel. -/

open _root_.MeasureTheory Metric Set Filter
open scoped Topology
noncomputable section
namespace OAI.Analysis.Fourier.Radial

def bochnerRieszKernel {n : ℕ} (p : ℝ) (x : Space n) : ℂ :=
  OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ : Space n => (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1 ξ : ℂ)) x

theorem integral_ball_bochnerRiesz_sine_eq_zero {n : ℕ} (p : ℝ) (x : Space n) :
    (∫ ξ, OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1 ξ * Real.sin (inner ℝ x ξ)
      ∂unitBallVolume n) = 0 := by
  let e : Space n ≃ₗᵢ[ℝ] Space n := LinearIsometryEquiv.neg ℝ
  have H := (measurePreserving_unitBall_orthogonal e).integral_comp
    e.toHomeomorph.measurableEmbedding (fun ξ => OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1 ξ *
      Real.sin (inner ℝ x ξ))
  have he (ξ : Space n) : e ξ = -ξ := rfl
  simp only [he, OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol, norm_neg, inner_neg_right,
    Real.sin_neg, mul_neg, integral_neg] at H
  unfold OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol
  linarith

theorem ball_bochnerRiesz_exp_eq_cosine {n : ℕ} {p : ℝ} (hp : 0 < p) (x : Space n) :
    (∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) *
      (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1 ξ : ℂ) ∂unitBallVolume n) =
      (ballCosineKernel (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1) x : ℂ) := by
  have hw := OAI.Analysis.Fourier.BochnerRiesz.continuous_bochnerRieszSymbol (n := n) hp.le 1
  have hi : Integrable (fun ξ : Space n => Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) *
      (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1 ξ : ℂ)) (unitBallVolume n) := by
    have hc : Continuous (fun ξ : Space n => Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) *
        (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1 ξ : ℂ)) := by fun_prop
    exact hc.continuousOn.integrableOn_compact (isCompact_closedBall 0 1)
  apply Complex.ext
  · change RCLike.re (∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) *
        (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1 ξ : ℂ) ∂unitBallVolume n) = _
    rw [← integral_re hi]
    change (∫ ξ, (Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) *
        (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1 ξ : ℂ)).re ∂unitBallVolume n) = _
    simp [Complex.exp_re, ballCosineKernel, mul_comm]
  · change RCLike.im (∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) *
        (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1 ξ : ℂ) ∂unitBallVolume n) = 0
    rw [← integral_im hi]
    change (∫ ξ, (Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) *
        (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1 ξ : ℂ)).im ∂unitBallVolume n) = 0
    simpa [Complex.exp_im, mul_comm] using integral_ball_bochnerRiesz_sine_eq_zero p x

theorem bochnerRieszKernel_eq_cosine {n : ℕ} {p : ℝ} (hp : 0 < p) (x : Space n) :
    bochnerRieszKernel p x = (((2 * Real.pi) ^ n)⁻¹ : ℝ) •
      (ballCosineKernel (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1) x : ℂ) := by
  unfold bochnerRieszKernel OAI.Analysis.Fourier.LocalSmoothing.angularInverse
  congr 1
  rw [← ball_bochnerRiesz_exp_eq_cosine hp]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro ξ hξ
  have hn : 1 < ‖ξ‖ := by simpa only [mem_closedBall, dist_zero_right, not_le] using hξ
  rw [bochnerRieszSymbol_unit_zero hp hn.le, Complex.ofReal_zero, mul_zero]

theorem abs_bochnerRiesz_ballKernel_le_mass {n : ℕ} {p : ℝ} (hp : 0 < p) (x : Space n) :
    |ballCosineKernel (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1) x| ≤
      ∫ ξ, OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1 ξ ∂unitBallVolume n := by
  have hw := OAI.Analysis.Fourier.BochnerRiesz.continuous_bochnerRieszSymbol (n := n) hp.le 1
  change ‖∫ ξ, OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1 ξ * Real.cos (inner ℝ x ξ)
    ∂unitBallVolume n‖ ≤ _
  calc
    _ ≤ ∫ ξ, ‖OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1 ξ * Real.cos (inner ℝ x ξ)‖
        ∂unitBallVolume n := norm_integral_le_integral_norm _
    _ ≤ _ := by
      apply integral_mono_ae (integrable_unitBallVolume (by fun_prop)) (integrable_unitBallVolume hw)
      filter_upwards [] with ξ
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol_nonneg p 1 ξ)]
      exact mul_le_of_le_one_right (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol_nonneg p 1 ξ)
        (Real.abs_cos_le_one _)

end OAI.Analysis.Fourier.Radial

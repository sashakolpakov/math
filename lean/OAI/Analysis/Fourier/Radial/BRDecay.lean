import OAI.Analysis.Fourier.Radial.BRAsymptotic
import OAI.Analysis.Fourier.Radial.BRFourier
import OAI.Analysis.Fourier.Radial.Decay

open OAI.Analysis.Fourier.Wave

/-! Sharp kernel decay and nonzero leading oscillations for Bochner--Riesz. -/

open _root_.MeasureTheory
noncomputable section
namespace OAI.Analysis.Fourier.Radial

theorem bochnerRiesz_ballKernel_polynomial_decay {n : ℕ} (hn : 1 ≤ n)
    {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : Space n,
      |ballCosineKernel (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1) x| ≤
        C * (1 + ‖x‖) ^ (-((n : ℝ) + 2 * p + 1) / 2) := by
  obtain ⟨A, B, D, hD, _, h⟩ := bochnerRiesz_ball_radial_asymptotic hn hp
  let M := ∫ ξ : Space n, OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1 ξ ∂unitBallVolume n
  let K := D + |A| + |B|
  have hM : 0 ≤ M := integral_nonneg (fun ξ => OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol_nonneg p 1 ξ)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hm : 0 ≤ ((n : ℝ) + 2 * p + 1) / 2 := by positivity
  refine ⟨(M + K + 1) * (2 : ℝ) ^ (((n : ℝ) + 2 * p + 1) / 2), by positivity, ?_⟩
  intro x
  convert decay_from_normalized_bound hm hM hK (norm_nonneg x)
    (abs_bochnerRiesz_ballKernel_le_mass hp x)
    (fun hx => normalized_asymptotic_bound hx hD (h x hx)) using 1
  ring_nf

theorem bochnerRieszKernel_polynomial_decay {n : ℕ} (hn : 1 ≤ n)
    {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : Space n,
      ‖bochnerRieszKernel p x‖ ≤ C * (1 + ‖x‖) ^ (-((n : ℝ) + 2 * p + 1) / 2) := by
  obtain ⟨C, hC, h⟩ := bochnerRiesz_ballKernel_polynomial_decay hn hp
  let c : ℝ := ((2 * Real.pi) ^ n)⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c * C, mul_pos hc hC, fun x => ?_⟩
  rw [bochnerRieszKernel_eq_cosine hp, norm_smul, Real.norm_eq_abs,
    abs_of_pos hc, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ c * (C * (1 + ‖x‖) ^ (-((n : ℝ) + 2 * p + 1) / 2)) :=
      mul_le_mul_of_nonneg_left (h x) hc.le
    _ = _ := by ring

theorem bochnerRieszKernel_asymptotic {n : ℕ} (hn : 1 ≤ n) {p : ℝ} (hp : 0 < p) :
    ∃ A B C : ℝ, 0 ≤ C ∧ 0 < A ^ 2 + B ^ 2 ∧ ∀ x : Space n, 1 ≤ ‖x‖ →
      ‖((‖x‖ ^ (((n : ℝ) + 2 * p + 1) / 2) : ℝ) : ℂ) * bochnerRieszKernel p x -
        ((A * Real.cos ‖x‖ + B * Real.sin ‖x‖ : ℝ) : ℂ)‖ ≤ C / ‖x‖ := by
  obtain ⟨A, B, C, hC, hAB, h⟩ := bochnerRiesz_ball_radial_asymptotic hn hp
  let c : ℝ := ((2 * Real.pi) ^ n)⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  have hABc : 0 < (c * A) ^ 2 + (c * B) ^ 2 := by
    have H := mul_pos (sq_pos_of_pos hc) hAB
    nlinarith
  refine ⟨c * A, c * B, c * C, mul_nonneg hc.le hC, hABc, fun x hx => ?_⟩
  have he : ((‖x‖ ^ (((n : ℝ) + 2 * p + 1) / 2) : ℝ) : ℂ) * bochnerRieszKernel p x -
      ((c * A * Real.cos ‖x‖ + c * B * Real.sin ‖x‖ : ℝ) : ℂ) =
      ((c * (‖x‖ ^ (((n : ℝ) + 2 * p + 1) / 2) *
        ballCosineKernel (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1) x -
        (A * Real.cos ‖x‖ + B * Real.sin ‖x‖)) : ℝ) : ℂ) := by
    rw [bochnerRieszKernel_eq_cosine hp]
    change _ * ((c : ℂ) * _) - _ = _
    push_cast
    ring
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hc]
  calc
    _ ≤ c * (C / ‖x‖) := mul_le_mul_of_nonneg_left (h x hx) hc.le
    _ = _ := by ring

end OAI.Analysis.Fourier.Radial

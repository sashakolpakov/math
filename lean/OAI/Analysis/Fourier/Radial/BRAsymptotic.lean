import OAI.Analysis.Fourier.Radial.BRODE
import OAI.Analysis.Fourier.Radial.Bessel

open OAI.Analysis.Fourier.Wave

/-! Nonzero leading oscillations of the Bochner--Riesz radial integral. -/

open _root_.MeasureTheory Metric Set Filter
open scoped Topology
noncomputable section
namespace OAI.Analysis.Fourier.Radial

theorem bochnerRiesz_weight_integral_pos {n : ℕ} {p : ℝ} (hp : 0 < p) :
    0 < ∫ ξ : Space n, OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1 ξ := by
  have hw := OAI.Analysis.Fourier.BochnerRiesz.continuous_bochnerRieszSymbol (n := n) hp.le 1
  apply hw.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)
    (hasCompactSupport_bochnerRieszSymbol_unit hp)
    (fun x => OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol_nonneg p 1 x)
  simp [OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol]

theorem bochnerRiesz_ball_kernel_one_pos {n : ℕ} {p : ℝ} (hp : 0 < p)
    {v : Space n} (hv : ‖v‖ = 1) :
    0 < ballCosineKernel (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1) v := by
  let w : Space n → ℝ := OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1
  have hw : Continuous w := OAI.Analysis.Fourier.BochnerRiesz.continuous_bochnerRieszSymbol hp.le 1
  have hwpos : 0 < ∫ ξ, w ξ ∂unitBallVolume n := by
    have H := integral_bochnerRiesz_mul_eq_ball (n := n) hp (fun _ => 1)
    simp only [mul_one] at H
    rw [← H]
    exact bochnerRiesz_weight_integral_pos hp
  have hb : ∀ᵐ ξ ∂unitBallVolume n, w ξ / 2 ≤ w ξ * Real.cos (inner ℝ v ξ) := by
    filter_upwards [ae_unitBall_inner_bound v] with ξ hξ
    rw [hv] at hξ
    have hsq : (inner ℝ v ξ) ^ 2 ≤ 1 := by
      have H := (sq_le_sq₀ (abs_nonneg (inner ℝ v ξ)) zero_le_one).mpr hξ
      simpa only [sq_abs, one_pow] using H
    have hc : (1 / 2 : ℝ) ≤ Real.cos (inner ℝ v ξ) := by
      linarith [Real.one_sub_sq_div_two_le_cos (x := inner ℝ v ξ)]
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hc
      (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol_nonneg p 1 ξ)
  have H := integral_mono_ae ((integrable_unitBallVolume hw).div_const 2)
    (integrable_unitBallVolume (by fun_prop)) hb
  rw [integral_div] at H
  exact (half_pos hwpos).trans_le H

theorem bochnerRiesz_ball_axis_asymptotic {n : ℕ} {p : ℝ} (hp : 0 < p)
    (b : OrthonormalBasis (Fin n) ℝ (Space n)) (i : Fin n) :
    ∃ A B C : ℝ, 0 ≤ C ∧ 0 < A ^ 2 + B ^ 2 ∧ ∀ r, 1 ≤ r →
      |r ^ (((n : ℝ) + 2 * p + 1) / 2) *
          ballCosineKernel (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1) (r • b i) -
        (A * Real.cos r + B * Real.sin r)| ≤ C / r ∧
      |r ^ (((n : ℝ) + 2 * p + 1) / 2) *
          ballCosineLineDeriv (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1) 0 (b i) r +
        (((n : ℝ) + 2 * p + 1) / 2) * r ^ (((n : ℝ) + 2 * p + 1) / 2 - 1) *
          ballCosineKernel (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1) (r • b i) -
        (-A * Real.sin r + B * Real.cos r)| ≤ C / r := by
  apply bessel_normalized_asymptotic
  · intro t _
    simpa only [zero_add] using hasDerivAt_ballCosineLine
      (OAI.Analysis.Fourier.BochnerRiesz.continuous_bochnerRieszSymbol hp.le 1) 0 (b i) t
  · intro t ht
    convert hasDerivAt_bochnerRiesz_ball_bessel hp b i (by linarith : 0 < t) using 1
    ring
  · left
    simpa only [one_smul] using (bochnerRiesz_ball_kernel_one_pos hp (b.norm_eq_one i)).ne'

theorem bochnerRiesz_ball_radial_asymptotic {n : ℕ} (hn : 1 ≤ n) {p : ℝ} (hp : 0 < p) :
    ∃ A B C : ℝ, 0 ≤ C ∧ 0 < A ^ 2 + B ^ 2 ∧ ∀ x : Space n, 1 ≤ ‖x‖ →
      |‖x‖ ^ (((n : ℝ) + 2 * p + 1) / 2) *
          ballCosineKernel (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1) x -
        (A * Real.cos ‖x‖ + B * Real.sin ‖x‖)| ≤ C / ‖x‖ := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let i : Fin n := ⟨0, by omega⟩
  obtain ⟨A, B, C, hC, hAB, h⟩ := bochnerRiesz_ball_axis_asymptotic hp b i
  refine ⟨A, B, C, hC, hAB, fun x hx => ?_⟩
  rw [ballCosineKernel_radial (fun e ξ => by
    simp only [OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol, e.norm_map]) (b.norm_eq_one i)]
  exact (h ‖x‖ hx).1

end OAI.Analysis.Fourier.Radial

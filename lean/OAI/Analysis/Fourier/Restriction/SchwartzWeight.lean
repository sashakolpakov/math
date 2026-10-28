import OAI.Analysis.Fourier.Restriction.PolynomialWeight

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Filter
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem integrable_schwartz_polynomial_weight {n : ℕ} (f : SchwartzMap (Space n) ℂ) {a : ℝ} (ha : 0 ≤ a) :
    Integrable (fun x ↦ ‖f x‖ * (1 + ‖x‖) ^ a) := by
  obtain ⟨k, hk⟩ := exists_nat_gt a
  have H : Integrable (fun x : Space n ↦ 2 ^ k * (‖f x‖ + ‖x‖ ^ k * ‖f x‖)) :=
    (f.integrable.norm.add (f.integrable_pow_mul volume k)).const_mul _
  apply H.mono'
  · fun_prop
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hpow : (1 + ‖x‖) ^ a ≤ (1 + ‖x‖) ^ k := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg x]) hk.le
  have hsum : (1 + ‖x‖) ^ k ≤ 2 ^ k * (1 + ‖x‖ ^ k) := by
    rcases le_total ‖x‖ 1 with hx | hx
    · have h1 : (1 + ‖x‖) ^ k ≤ 2 ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
      have h2 : 0 ≤ ‖x‖ ^ k := by positivity
      nlinarith [show 0 ≤ (2 : ℝ) ^ k by positivity]
    · have h1 : (1 + ‖x‖) ^ k ≤ (2 * ‖x‖) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
      rw [mul_pow] at h1
      nlinarith [show 0 ≤ (2 : ℝ) ^ k by positivity]
  calc
    _ ≤ ‖f x‖ * (2 ^ k * (1 + ‖x‖ ^ k)) := mul_le_mul_of_nonneg_left (hpow.trans hsum) (norm_nonneg _)
    _ = _ := by ring

end OAI.Analysis.Fourier.Restriction

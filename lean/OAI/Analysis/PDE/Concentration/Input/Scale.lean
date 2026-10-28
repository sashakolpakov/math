import Mathlib

noncomputable section
namespace OAI.Analysis.PDE.Concentration

theorem input_rpow_square (d : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    (L ^ (-(d : ℝ) / 2)) ^ 2 = (L ^ d)⁻¹ := by
  rw [← Real.rpow_mul_natCast hL]
  rw [show -(d : ℝ) / 2 * (2 : ℕ) = -(d : ℝ) by norm_num]
  rw [Real.rpow_neg hL, Real.rpow_natCast]

theorem input_density_scaling (d : ℕ) {h L : ℝ} (hh : 0 < h) (hL : 0 < L) :
    (h * L) ^ (2 * (d + 1)) * ((h ^ d)⁻¹ * L ^ (-(d : ℝ) / 2)) ^ 2 =
      h ^ 2 * L ^ (d + 2) := by
  rw [mul_pow, mul_pow, input_rpow_square d hL.le, inv_pow]
  rw [show 2 * (d + 1) = d * 2 + 2 by omega, pow_add, pow_add, pow_mul]
  rw [show d + 2 = d + 2 from rfl, pow_add]
  have hh' : h ^ d ≠ 0 := pow_ne_zero _ hh.ne'
  have hL' : L ^ d ≠ 0 := pow_ne_zero _ hL.ne'
  rw [pow_mul]
  field_simp

end OAI.Analysis.PDE.Concentration

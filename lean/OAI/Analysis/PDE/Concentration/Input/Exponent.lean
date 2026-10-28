import OAI.Analysis.PDE.Concentration.Input.Sup

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set OAI.Analysis.Calculus.Current

theorem input_multiplier_square (d : ℕ) {h L : ℝ} (hL : 0 ≤ L) :
    (((h ^ d)⁻¹ * L ^ (((gaussianDerivativeOrder d : ℕ) : ℝ) / 2 - d / 2)) ^ 2) =
      ((h ^ d)⁻¹) ^ 2 * L ^ (d + 6) := by
  rw [mul_pow, ← Real.rpow_mul_natCast hL]
  congr 1
  rw [← Real.rpow_natCast]
  congr 1
  simp only [gaussianDerivativeOrder, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  ring

theorem input_regularization_error_le_one (d : ℕ) {h L : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (hL : 1 ≤ L) :
    h ^ (50 * (d + 1)) / (h * L) ^ (2 * (d + 1)) ≤ 1 := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  apply (div_le_one (pow_pos (mul_pos hh hL0) _)).mpr
  exact (pow_le_pow_of_le_one hh.le hh1 (by omega : 2 * (d + 1) ≤ 50 * (d + 1))).trans
    (pow_le_pow_left₀ hh.le (by nlinarith : h ≤ h * L) _)

theorem input_multiplier_square_ge_one (d : ℕ) {h L : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (hL : 1 ≤ L) :
    1 ≤ ((h ^ d)⁻¹) ^ 2 * L ^ (d + 6) := by
  have hp : 0 < h ^ d := pow_pos hh d
  have hq : h ^ d ≤ 1 := pow_le_one₀ hh.le hh1
  have hi : 1 ≤ (h ^ d)⁻¹ := (one_le_inv₀ hp).mpr hq
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hi) (one_le_pow₀ hL)

/-- The exact logarithmic exponent in the source barrier. Here the frequency
dimension is `d` and the differentiability order is `M = 2(d+3)`. -/
theorem input_barrier_power (d : ℕ) (hd : 0 < d) {h L : ℝ}
    (hh : 0 < h) (hL : 0 < L) (B c : ℝ) :
    (B * L ^ (1 + (gaussianDerivativeOrder d : ℝ) / d) * (c / (h * L) ^ 2)) ^ d =
      (B * c) ^ d * ((h ^ d)⁻¹) ^ 2 * L ^ (d + 6) := by
  have hd0 : (d : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hd)
  have hp : (L ^ (1 + (gaussianDerivativeOrder d : ℝ) / d)) ^ d = L ^ (3 * d + 6) := by
    rw [← Real.rpow_mul_natCast hL.le, ← Real.rpow_natCast]
    congr 1
    simp only [gaussianDerivativeOrder, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
    field_simp
    ring
  rw [mul_pow, mul_pow, hp, div_pow, mul_pow]
  rw [show 3 * d + 6 = (d + 6) + 2 * d by omega, pow_add, pow_mul]
  simp only [mul_pow]
  field_simp
  ring

theorem exists_input_barrier_coefficient (d : ℕ) (hd : 0 < d)
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c) :
    ∃ B : ℝ, 0 < B ∧ ∀ (h L : ℝ), 0 < h → h ≤ 1 → 1 ≤ L →
      C * (((h ^ d)⁻¹ * L ^ (((gaussianDerivativeOrder d : ℕ) : ℝ) / 2 - d / 2)) ^ 2 +
        h ^ (50 * (d + 1)) / (h * L) ^ (2 * (d + 1))) ≤
      (B * L ^ (1 + (gaussianDerivativeOrder d : ℝ) / d) * (c / (h * L) ^ 2)) ^ d := by
  refine ⟨(2 * C + 1) / c, by positivity, ?_⟩
  intro h L hh hh1 hL
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  rw [input_multiplier_square d hL0.le, input_barrier_power d hd hh hL0]
  have hcoef : 2 * C ≤ (((2 * C + 1) / c) * c) ^ d := by
    rw [div_mul_cancel₀ _ hc.ne']
    exact (by linarith : 2 * C ≤ 2 * C + 1).trans
      (le_self_pow₀ (by linarith : 1 ≤ 2 * C + 1) hd.ne')
  have herr := input_regularization_error_le_one d hh hh1 hL
  have hmain := input_multiplier_square_ge_one d hh hh1 hL
  have hm0 : 0 ≤ ((h ^ d)⁻¹) ^ 2 * L ^ (d + 6) := by positivity
  have hbound := mul_le_mul_of_nonneg_right hcoef hm0
  nlinarith

end OAI.Analysis.PDE.Concentration

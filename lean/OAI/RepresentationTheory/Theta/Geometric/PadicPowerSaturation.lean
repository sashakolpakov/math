import Mathlib.NumberTheory.Padics.PadicIntegers

/-! # Padic Power Saturation -/

namespace OAI.RepresentationTheory.Theta.Geometric.PadicPowerSaturation

noncomputable section

/-! A rational number integral at q and with only a q-power denominator
is an integer. The proof uses literal integer divisibility. -/

theorem rational_power_saturation (q : ℕ) [Fact q.Prime] (a : ℚ)
    (ha : ‖(a : ℚ_[q])‖ ≤ 1) (n : ℕ) (z : ℤ) (hz : (q : ℚ) ^ n * a = z) :
    ∃ w : ℤ, a = w := by
  have hnorm : ‖(z : ℚ_[q])‖ ≤ (q : ℝ) ^ (-n : ℤ) := by
    have hz' : (q : ℚ_[q]) ^ n * (a : ℚ_[q]) = z := by exact_mod_cast hz
    rw [← hz', norm_mul, Padic.norm_p_pow]
    exact (mul_le_mul_of_nonneg_left ha (zpow_nonneg (Nat.cast_nonneg q) _)).trans_eq (mul_one _)
  obtain ⟨w, hw⟩ := (Padic.norm_int_le_pow_iff_dvd (p := q) z n).mp hnorm
  refine ⟨w, ?_⟩
  have hqw : (q : ℚ) ^ n * a = (q : ℚ) ^ n * (w : ℚ) := by
    rw [hz, hw, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  exact mul_left_cancel₀ (pow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)) hqw

end

end OAI.RepresentationTheory.Theta.Geometric.PadicPowerSaturation

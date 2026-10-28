import OAI.Analysis.Fourier.SquareFunction.Square.L2

open _root_.MeasureTheory Set
open scoped ENNReal

namespace OAI.Analysis.Fourier.SquareFunction

theorem radius_log_measure_scaling (F : ℝ → ℝ≥0∞) {c : ℝ} (hc : 0 < c) :
    (∫⁻ r in Ioi 0, F (c * r) / ENNReal.ofReal r) =
      ∫⁻ r in Ioi 0, F r / ENNReal.ofReal r := by
  have hImage : (fun r : ℝ => c * r) '' Ioi 0 = Ioi 0 := by
    ext r
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact mul_pos hc hs
    · intro hr
      refine ⟨r / c, div_pos hr hc, ?_⟩
      field_simp
  have h := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (fun r (hr : r ∈ Ioi (0 : ℝ)) =>
      (hasDerivAt_mul_const c).hasDerivWithinAt)
    (show InjOn (fun r : ℝ => r * c) (Ioi 0) from
      (mul_left_injective₀ hc.ne').injOn)
    (fun r => F r / ENNReal.ofReal r)
  have hImage' : (fun r : ℝ => r * c) '' Ioi 0 = Ioi 0 := by
    simpa only [mul_comm] using hImage
  rw [hImage'] at h
  rw [h]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp
  rw [abs_of_pos hc, ENNReal.ofReal_mul (le_of_lt hr)]
  rw [mul_comm r c, mul_comm (ENNReal.ofReal r) (ENNReal.ofReal c)]
  rw [← mul_div_assoc]
  exact (ENNReal.mul_div_mul_left (F (c * r)) (ENNReal.ofReal r)
    (by positivity) ENNReal.ofReal_ne_top).symm

theorem radiusMultiplier_scale {c : ℝ} (hc : 0 < c) (α ρ r : ℝ) :
    radiusMultiplier α (c * ρ) (c * r) = radiusMultiplier α ρ r := by
  unfold radiusMultiplier
  simp only [show c * ρ < c * r ↔ ρ < r by constructor <;> intro h <;> nlinarith]
  split_ifs
  · have he : (c * ρ) ^ 2 / (c * r) ^ 2 = ρ ^ 2 / r ^ 2 := by
      simp only [mul_pow]
      exact mul_div_mul_left _ _ (pow_ne_zero 2 hc.ne')
    rw [he]
  · rfl

end OAI.Analysis.Fourier.SquareFunction

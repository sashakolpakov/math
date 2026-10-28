import OAI.Analysis.Calculus.Current.Fiber.Height

/-! Comparability of the null height with the physical imaginary time. -/

noncomputable section
namespace OAI.Analysis.Calculus.Current

theorem fiberDenominator_norm_lower {d : ℕ} (a : ℝ) (z : Index d → ℂ)
    (hr : fiberDefining (1 / 10) a z ≤ 0) :
    (199 / 200 : ℝ) ≤ ‖fiberDenominator (ratio z)‖ := by
  have hq := (norm_fiberQuadratic_le (ratio z)).trans
    (fiber_ratio_bound (1 / 10) a z (by norm_num) hr)
  have hd : ‖(1 : ℂ) - fiberDenominator (ratio z)‖ ≤ (1 / 200 : ℝ) := by
    have he : (1 : ℂ) - fiberDenominator (ratio z) = - (fiberQuadratic (ratio z) / 2) := by
      unfold fiberDenominator
      ring
    rw [he, norm_neg, norm_div]
    norm_num
    linarith
  have hn := norm_sub_norm_le (1 : ℂ) (fiberDenominator (ratio z))
  norm_num at hn
  linarith

theorem fiber_height_upper_of_null_time {d : ℕ} (a : ℝ) (ha : 0 < a)
    (z : Index d → ℂ) (hr : fiberDefining (1 / 10) a z ≤ 0)
    (ht : a ≤ ‖z none - z (some none)‖) :
    ‖z none‖ ≤ 2 * ‖z none - z (some none)‖ := by
  have he := congrArg norm (fiberDenominator_mul_height z)
  rw [norm_mul] at he
  have hb := norm_add_le (z none - z (some none)) (phi z)
  rw [← he] at hb
  have hl := mul_le_mul_of_nonneg_right (fiberDenominator_norm_lower a z hr) (norm_nonneg (z none))
  have hf := fiber_phase_norm_le a ha z hr
  nlinarith [norm_nonneg (z none - z (some none))]

theorem imaginaryTime_norm {d : ℕ} (z : Index d → ℂ) :
    ‖z none - z (some none)‖ = ‖imaginaryTime z‖ * Real.sqrt 2 := by
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  simp [imaginaryTime, abs_of_nonneg (Real.sqrt_nonneg _), hs]

theorem fiber_height_le_time {d : ℕ} (a : ℝ) (ha : 0 < a)
    (z : Index d → ℂ) (hr : fiberDefining (1 / 10) a z ≤ 0)
    (ht : a ≤ ‖imaginaryTime z‖) : ‖z none‖ ≤ 3 * ‖imaginaryTime z‖ := by
  have hs₁ : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hs₂ : Real.sqrt 2 ≤ (3 / 2 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have ht' : a ≤ ‖z none - z (some none)‖ := by
    rw [imaginaryTime_norm]
    exact ht.trans (le_mul_of_one_le_right (norm_nonneg _) hs₁)
  have hy := fiber_height_upper_of_null_time a ha z hr ht'
  rw [imaginaryTime_norm] at hy
  nlinarith [mul_le_mul_of_nonneg_left hs₂ (norm_nonneg (imaginaryTime z))]

end OAI.Analysis.Calculus.Current

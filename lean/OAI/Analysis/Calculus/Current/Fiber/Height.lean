import OAI.Analysis.Calculus.Current.Flux

/-! The lower height bound follows from the actual fiber and time inequalities. -/

noncomputable section
namespace OAI.Analysis.Calculus.Current

open OAI.Analysis.Calculus.Quaternion
open scoped Matrix Matrix.Norms.Elementwise

def imaginaryTime {d : ℕ} (z : Index d → ℂ) : ℂ :=
  (z none - z (some none)) / (Real.sqrt 2 : ℂ)

theorem fiberDenominator_mul_height {d : ℕ} (z : Index d → ℂ) :
    fiberDenominator (ratio z) * z none = z none - z (some none) + phi z := by
  by_cases hY : z none = 0
  · simp [fiberDenominator, fiberQuadratic, ratio, phi, hY]
  · simp only [fiberDenominator, fiberQuadratic, ratio, phi]
    simp_rw [div_mul_div_comm]
    rw [← Finset.sum_div]
    field_simp
    ring

theorem fiber_phase_norm_le {d : ℕ} (a : ℝ) (ha : 0 < a) (z : Index d → ℂ)
    (hr : fiberDefining (1 / 10) a z ≤ 0) : ‖phi z‖ ≤ a / 10 := by
  have hf := fiberMap_coordinate_norm_le_one (1 / 10) a z hr none
  have hf' : 10 * ‖phi z‖ / a ≤ 1 := by
    simpa [fiberMap, norm_div, norm_mul, abs_of_pos ha] using hf
  have := (div_le_iff₀ ha).mp hf'
  linarith

theorem fiberDenominator_norm_le {d : ℕ} (a : ℝ) (z : Index d → ℂ)
    (hr : fiberDefining (1 / 10) a z ≤ 0) :
    ‖fiberDenominator (ratio z)‖ ≤ 201 / 200 := by
  have hq := (norm_fiberQuadratic_le (ratio z)).trans
    (fiber_ratio_bound (1 / 10) a z (by norm_num) hr)
  calc
    _ ≤ ‖(1 : ℂ)‖ + ‖fiberQuadratic (ratio z) / 2‖ := norm_add_le _ _
    _ ≤ _ := by simp only [norm_one, norm_div]; norm_num; linarith

theorem fiber_time_norm_le {d : ℕ} (a : ℝ) (ha : 0 < a) (z : Index d → ℂ)
    (hr : fiberDefining (1 / 10) a z ≤ 0) :
    ‖z none - z (some none)‖ ≤ (201 / 200) * ‖z none‖ + a / 10 := by
  have he : z none - z (some none) = fiberDenominator (ratio z) * z none - phi z := by
    rw [fiberDenominator_mul_height]
    ring
  rw [he]
  calc
    _ ≤ ‖fiberDenominator (ratio z) * z none‖ + ‖phi z‖ := norm_sub_le _ _
    _ ≤ _ := by
      rw [norm_mul]
      exact add_le_add (mul_le_mul_of_nonneg_right (fiberDenominator_norm_le a z hr)
        (norm_nonneg _)) (fiber_phase_norm_le a ha z hr)

theorem fiber_height_lower_of_null_time {d : ℕ} (a : ℝ) (ha : 0 < a)
    (z : Index d → ℂ) (hr : fiberDefining (1 / 10) a z ≤ 0)
    (ht : (6 / 5) * a ≤ ‖z none - z (some none)‖) : a ≤ ‖z none‖ := by
  have hu := fiber_time_norm_le a ha z hr
  nlinarith [norm_nonneg (z none)]

/-- This discharges the height hypothesis used by the quantitative current
bounds from the paper's actual condition `a ≤ |τ|`. -/
theorem fiber_height_ge_scale {d : ℕ} (a : ℝ) (ha : 0 < a)
    (z : Index d → ℂ) (hr : fiberDefining (1 / 10) a z ≤ 0)
    (ht : a ≤ ‖imaginaryTime z‖) : a ≤ ‖z none‖ := by
  apply fiber_height_lower_of_null_time a ha z hr
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs' : (6 / 5 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have ht' : a ≤ ‖z none - z (some none)‖ / Real.sqrt 2 := by
    simpa [imaginaryTime, norm_div, abs_of_pos hs] using ht
  have hmul := (le_div_iff₀ hs).mp ht'
  nlinarith [mul_le_mul_of_nonneg_right hs' ha.le]

end OAI.Analysis.Calculus.Current

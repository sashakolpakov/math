import OAI.Analysis.Fourier.LocalSmoothing.DyadicCutoff
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed

open Filter
open scoped Topology
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing

def smoothingDyadicLog (j : ℕ) : ℝ := 1 + Real.log (1 / smoothingDyadicScale j)

theorem smoothingDyadicLog_eq (j : ℕ) :
    smoothingDyadicLog j = 1 + (j : ℝ) * Real.log 2 := by
  simp [smoothingDyadicLog, smoothingDyadicScale, Real.log_pow]

theorem smoothingDyadicLog_pos (j : ℕ) : 0 < smoothingDyadicLog j := by
  rw [smoothingDyadicLog_eq]
  positivity

theorem log_two_le_one : Real.log 2 ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at h ⊢
  exact h

theorem smoothingDyadicLog_le (j : ℕ) : smoothingDyadicLog j ≤ (j : ℝ) + 1 := by
  rw [smoothingDyadicLog_eq]
  nlinarith [log_two_le_one, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

theorem smoothingDyadicLog_ge (j : ℕ) :
    Real.log 2 * ((j : ℝ) + 1) ≤ smoothingDyadicLog j := by
  rw [smoothingDyadicLog_eq]
  nlinarith [log_two_le_one]

theorem smoothingDyadicScale_rpow (j : ℕ) (ε : ℝ) :
    smoothingDyadicScale j ^ ε = ((2 : ℝ)⁻¹ ^ ε) ^ j := by
  rw [smoothingDyadicScale, ← Real.rpow_natCast_mul (by norm_num)]
  rw [mul_comm (j : ℝ) ε, Real.rpow_mul_natCast (by norm_num)]

theorem summable_smoothing_log_rpow {q : ℝ} (hq : q < -1) :
    Summable (fun j : ℕ ↦ smoothingDyadicLog j ^ q) := by
  have hs : Summable (fun j : ℕ ↦ ((j : ℝ) + 1) ^ q) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hq)
  have hc := hs.mul_left (Real.log 2 ^ q)
  apply Summable.of_nonneg_of_le
    (fun j ↦ Real.rpow_nonneg (smoothingDyadicLog_pos j).le q) (fun j ↦ ?_) hc
  calc
    smoothingDyadicLog j ^ q ≤ (Real.log 2 * ((j : ℝ) + 1)) ^ q :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (smoothingDyadicLog_ge j) (by linarith)
    _ = Real.log 2 ^ q * ((j : ℝ) + 1) ^ q :=
      Real.mul_rpow (Real.log_pos (by norm_num)).le (by positivity)

theorem summable_smoothing_log_weights (A : ℕ) {B : ℝ} (hB : (A : ℝ) + 1 < B) :
    Summable (fun j : ℕ ↦ smoothingDyadicLog j ^ A * smoothingDyadicLog j ^ (-B)) := by
  have he (j : ℕ) : smoothingDyadicLog j ^ A * smoothingDyadicLog j ^ (-B) =
      smoothingDyadicLog j ^ ((A : ℝ) - B) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (smoothingDyadicLog_pos j)]
    congr 1
  simp_rw [he]
  exact summable_smoothing_log_rpow (by linarith)

theorem summable_shifted_pow_mul_geometric (A : ℕ) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    Summable (fun j : ℕ ↦ ((j : ℝ) + 1) ^ A * r ^ j) := by
  have hs := summable_pow_mul_geometric_of_norm_lt_one A
    (show ‖r‖ < 1 by rwa [Real.norm_eq_abs, abs_of_pos hr])
  have ht := ((summable_nat_add_iff 1).mpr hs).mul_left r⁻¹
  convert ht using 1
  funext j
  simp only [Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp

theorem summable_smoothing_sobolev_weights (A : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Summable (fun j : ℕ ↦ smoothingDyadicScale j ^ ε * smoothingDyadicLog j ^ A) := by
  let r : ℝ := (2 : ℝ)⁻¹ ^ ε
  have hr : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hε
  have hs := summable_shifted_pow_mul_geometric A hr hr1
  apply Summable.of_nonneg_of_le
    (fun j ↦ mul_nonneg (Real.rpow_nonneg (smoothingDyadicScale_pos j).le ε)
      (pow_nonneg (smoothingDyadicLog_pos j).le A)) (fun j ↦ ?_) hs
  rw [smoothingDyadicScale_rpow]
  change r ^ j * smoothingDyadicLog j ^ A ≤ ((j : ℝ) + 1) ^ A * r ^ j
  rw [mul_comm (r ^ j)]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (smoothingDyadicLog_pos j).le (smoothingDyadicLog_le j) A)
    (pow_nonneg hr.le j)

end OAI.Analysis.Fourier.LocalSmoothing

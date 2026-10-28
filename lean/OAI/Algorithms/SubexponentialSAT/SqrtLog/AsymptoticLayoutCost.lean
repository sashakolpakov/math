import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.AsymptoticLayoutFeasibility
import OAI.Algorithms.SubexponentialSAT.SqrtLog.AsymptoticLayoutLabels

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

theorem eventually_layout_inverse_target :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) / layoutR n ≤ 128 * Statement.runtimeScale n := by
  filter_upwards [eventually_inverse_schedule_target, eventually_le_s 1] with n hn hs
  have hs' : (0 : ℝ) < s n := by exact_mod_cast (by omega : 0 < s n)
  have hr : (s n : ℝ) ≤ layoutR n := by exact_mod_cast le_max_right 2 (s n)
  exact (div_le_div_of_nonneg_left (Nat.cast_nonneg n) hs' hr).trans hn

theorem eventually_cutoff_ratio (b : ℕ → ℕ) (q : ℕ)
    (hb : ∀ᶠ n : ℕ in atTop, b n ≤ L n ^ q) :
    ∀ᶠ n : ℕ in atTop,
      (layoutCutoff n (b n) : ℝ) / layoutQ n ≤
        (128 * (28 * q + 312) : ℕ) * (w n : ℝ) / Real.sqrt (L n : ℝ) := by
  filter_upwards [eventually_layoutCutoff_sq_le b q hb,
    eventually_layoutQ_comparison, eventually_layoutQ_ge 1] with n hsq hcomp hQ
  have hQ' : (0 : ℝ) < layoutQ n := by exact_mod_cast (by omega : 0 < layoutQ n)
  have hL : (0 : ℝ) < L n := by exact_mod_cast L_pos n
  have hroot0 : 0 < Real.sqrt (L n : ℝ) := Real.sqrt_pos.2 hL
  have hroot := Real.sq_sqrt hL.le
  have hsq' : (layoutCutoff n (b n) : ℝ) ^ 2 ≤ (28 * q + 312 : ℕ) * (L n : ℝ) := by
    exact_mod_cast hsq
  have hK : (1 : ℝ) ≤ (28 * q + 312 : ℕ) := by norm_cast; omega
  have hR : (layoutCutoff n (b n) : ℝ) ≤
      (28 * q + 312 : ℕ) * Real.sqrt (L n : ℝ) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    calc
      (layoutCutoff n (b n) : ℝ) ^ 2 ≤ (28 * q + 312 : ℕ) * (L n : ℝ) := hsq'
      _ ≤ ((28 * q + 312 : ℕ) : ℝ) ^ 2 * (L n : ℝ) :=
        mul_le_mul_of_nonneg_right (by nlinarith) hL.le
      _ = ((28 * q + 312 : ℕ) * Real.sqrt (L n : ℝ)) ^ 2 := by rw [mul_pow, hroot]
  have hprod := mul_le_mul_of_nonneg_right hR hroot0.le
  have hprod' : (layoutCutoff n (b n) : ℝ) * Real.sqrt (L n : ℝ) ≤
      (28 * q + 312 : ℕ) * (L n : ℝ) := by
    calc
      _ ≤ (28 * q + 312 : ℕ) * Real.sqrt (L n : ℝ) * Real.sqrt (L n : ℝ) := hprod
      _ = _ := by rw [mul_assoc, ← pow_two, hroot]
  have hcomp' : (L n : ℝ) ≤ 128 * (layoutQ n : ℝ) * w n := by exact_mod_cast hcomp.1
  have hm := mul_le_mul_of_nonneg_left hcomp' (show (0 : ℝ) ≤ (28 * q + 312 : ℕ) by positivity)
  apply (div_le_div_iff₀ hQ' hroot0).2
  convert hprod'.trans hm using 1 ; push_cast ; ring

/-- The spectral numerator times the logarithmic support-entropy loss fits
the exact target. Any further fixed coefficient may multiply this bound. -/
theorem eventually_layout_spectral_cost (b : ℕ → ℕ) (q : ℕ)
    (hb : ∀ᶠ n : ℕ in atTop, b n ≤ L n ^ q) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * ((layoutCutoff n (b n) : ℝ) / layoutQ n) * w n ≤
        (8192 * (28 * q + 312) : ℕ) * Statement.runtimeScale n := by
  filter_upwards [eventually_cutoff_ratio b q hb] with n hn
  have ht := four_le_logSize n
  have hW := two_le_logLogSize n
  have hroots : Real.sqrt (logSize n) ≤ Real.sqrt (L n : ℝ) :=
    Real.sqrt_le_sqrt (logSize_lt_L n).le
  have hrootpos : 0 < Real.sqrt (logSize n) := Real.sqrt_pos.2 (by linarith)
  have hw := w_le_twice_logLogSize n
  have hmain : (n : ℝ) * ((layoutCutoff n (b n) : ℝ) / layoutQ n) * w n ≤
      (512 * (28 * q + 312) : ℕ) * binaryScale n := by
    calc
      _ ≤ (n : ℝ) * (((128 * (28 * q + 312) : ℕ) : ℝ) * w n /
          Real.sqrt (L n : ℝ)) * w n := by gcongr
      _ ≤ (n : ℝ) * (((128 * (28 * q + 312) : ℕ) : ℝ) * (2 * logLogSize n) /
          Real.sqrt (logSize n)) * (2 * logLogSize n) := by gcongr
      _ = _ := by unfold binaryScale; push_cast; ring
  have htarget := binaryScale_le_target n
  have hm := mul_le_mul_of_nonneg_left htarget
    (show (0 : ℝ) ≤ (512 * (28 * q + 312) : ℕ) by positivity)
  push_cast at hmain hm ⊢
  nlinarith

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms

import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.AsymptoticOverhead
import OAI.Algorithms.SubexponentialSAT.SqrtLog.StatementScale

namespace OAI.Algorithms

/-! Conversion to the exact natural-logarithm target and absorption of
fixed polylogarithmic construction, search, and arithmetic overheads. -/

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

theorem log_two_bounds : (1 : ℝ) / 2 ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  · have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h

theorem logSize_natural_bounds (n : ℕ) :
    Real.log ((n : ℝ) + 16) ≤ logSize n ∧
      logSize n ≤ 2 * Real.log ((n : ℝ) + 16) := by
  have hpos := Statement.log_shift_pos n
  have hb := log_two_bounds
  have htwo : 0 < Real.log (2 : ℝ) := by linarith
  unfold logSize Real.logb
  constructor
  · apply (le_div_iff₀ htwo).2
    nlinarith
  · apply (div_le_iff₀ htwo).2
    nlinarith

theorem logLogSize_le_natural (n : ℕ) :
    logLogSize n ≤ 4 * Real.log (Real.log ((n : ℝ) + 16)) := by
  have ha := Statement.two_le_log_shift n
  have hap := Statement.log_shift_pos n
  have hb := log_two_bounds
  have htwo : 0 < Real.log (2 : ℝ) := by linarith
  have hlog : Real.log 2 ≤ Real.log (Real.log ((n : ℝ) + 16)) :=
    Real.log_le_log (by norm_num) ha
  have ht : 0 < logSize n := by have := four_le_logSize n; linarith
  have htlog : Real.log (logSize n) ≤
      Real.log 2 + Real.log (Real.log ((n : ℝ) + 16)) := by
    calc
      Real.log (logSize n) ≤ Real.log (2 * Real.log ((n : ℝ) + 16)) :=
        Real.log_le_log ht (logSize_natural_bounds n).2
      _ = _ := Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hap.ne'
  unfold logLogSize Real.logb
  apply (div_le_iff₀ htwo).2
  nlinarith

theorem binaryScale_le_target (n : ℕ) :
    binaryScale n ≤ 16 * Statement.runtimeScale n := by
  have hW := logLogSize_le_natural n
  have hW0 : 0 ≤ logLogSize n := by have := two_le_logLogSize n; linarith
  have hroot := Real.sqrt_le_sqrt (logSize_natural_bounds n).1
  have ha := Statement.sqrt_log_shift_pos n
  have hb : 0 < Real.sqrt (logSize n) := by linarith
  have hsq : logLogSize n ^ 2 ≤
      16 * Real.log (Real.log ((n : ℝ) + 16)) ^ 2 := by nlinarith
  unfold binaryScale Statement.runtimeScale
  calc
    (n : ℝ) * logLogSize n ^ 2 / Real.sqrt (logSize n) ≤
        (n : ℝ) * (16 * Real.log (Real.log ((n : ℝ) + 16)) ^ 2) /
          Real.sqrt (Real.log ((n : ℝ) + 16)) := by gcongr
    _ = _ := by ring

theorem eventually_inverse_schedule_target :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) / s n ≤ 128 * Statement.runtimeScale n := by
  filter_upwards [eventually_inverse_schedule_le] with n hn
  have h := binaryScale_le_target n
  linarith

theorem eventually_polylog_le_target (q : ℕ) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, C * logSize n ^ q ≤ Statement.runtimeScale n := by
  filter_upwards [eventually_logSize_power_le q (show 0 < 16 * C by positivity)] with n hn
  have h := binaryScale_le_target n
  nlinarith

theorem eventually_search_exponent_target (q : ℕ) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop,
      C * ((s n : ℝ) + 2) ^ q * Real.logb 2 ((n : ℝ) + 1) ≤
        Statement.runtimeScale n := by
  filter_upwards [eventually_schedule_search_exponent q
    (show 0 < 16 * C by positivity)] with n hn
  have h := binaryScale_le_target n
  nlinarith

theorem eventually_variable_search_target (degree : ℕ → ℕ) (q : ℕ)
    {C : ℝ} (hC : 0 < C)
    (hdegree : ∀ᶠ n : ℕ in atTop, (degree n : ℝ) ≤ C * ((s n : ℝ) + 2) ^ q) :
    ∀ᶠ n : ℕ in atTop,
      (((n + 1) ^ degree n : ℕ) : ℝ) ≤ (2 : ℝ) ^ Statement.runtimeScale n := by
  filter_upwards [hdegree, eventually_search_exponent_target q hC] with n hd hn
  have hl0 : 0 ≤ Real.logb 2 ((n : ℝ) + 1) :=
    Real.logb_nonneg (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hexp := (mul_le_mul_of_nonneg_right hd hl0).trans hn
  have heq : (((n + 1) ^ degree n : ℕ) : ℝ) =
      (2 : ℝ) ^ ((degree n : ℝ) * Real.logb 2 ((n : ℝ) + 1)) := by
    simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    rw [← Real.rpow_natCast]
    exact SubexpExponentArithmetic.rpow_eq_two_rpow_logb (by positivity) _
  rw [heq]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp

/-- Any explicitly bounded fixed polylogarithm is absorbed, irrespective of
which stage of the construction produced it. -/
theorem eventually_polylog_bounded_target (f : ℕ → ℝ) (q : ℕ)
    {C : ℝ} (hC : 0 < C)
    (hf : ∀ᶠ n : ℕ in atTop, f n ≤ C * logSize n ^ q) :
    ∀ᶠ n : ℕ in atTop, f n ≤ Statement.runtimeScale n := by
  filter_upwards [hf, eventually_polylog_le_target q hC] with n hn hb
  exact hn.trans hb

theorem eventually_exp_polylog_target (f : ℕ → ℝ) (q : ℕ)
    {C : ℝ} (hC : 0 < C)
    (hf : ∀ᶠ n : ℕ in atTop, f n ≤ C * logSize n ^ q) :
    ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ f n ≤ (2 : ℝ) ^ Statement.runtimeScale n := by
  filter_upwards [eventually_polylog_bounded_target f q hC hf] with n hn
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hn

theorem eventually_natural_log_power_target (q : ℕ) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop,
      C * Real.log ((n : ℝ) + 16) ^ q ≤ Statement.runtimeScale n := by
  filter_upwards [eventually_polylog_le_target q hC] with n hn
  exact (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Statement.log_shift_pos n).le (logSize_natural_bounds n).1 q)
    hC.le).trans hn

/-- Numerical finite-prefix absorption. This does not construct or dispatch
a small-input machine; it only supplies the uniform multiplicative constant
once the work at each exceptional dimension has already been bounded. -/
theorem finite_prefix_absorption (f : ℕ → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hf : ∀ᶠ n : ℕ in atTop, f n ≤ (2 : ℝ) ^ (A * Statement.runtimeScale n)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, f n ≤ C * (2 : ℝ) ^ (A * Statement.runtimeScale n) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hf
  let C : ℝ := (∑ i ∈ Finset.range N, |f i|) + 1
  have hsum : 0 ≤ ∑ i ∈ Finset.range N, |f i| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hC : 1 ≤ C := by dsimp [C]; linarith
  refine ⟨C, by linarith, ?_⟩
  intro n
  have he : 1 ≤ (2 : ℝ) ^ (A * Statement.runtimeScale n) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg hA (Statement.runtimeScale_nonneg n))
  by_cases hn : N ≤ n
  · exact (hN n hn).trans (le_mul_of_one_le_left (by positivity) hC)
  · have hnmem : n ∈ Finset.range N := Finset.mem_range.2 (by omega)
    have hfn : |f n| ≤ ∑ i ∈ Finset.range N, |f i| :=
      Finset.single_le_sum (f := fun i : ℕ => |f i|) (fun _ _ => abs_nonneg _) hnmem
    have hsmall : f n ≤ C := by have := le_abs_self (f n); dsimp [C]; linarith
    exact hsmall.trans (le_mul_of_one_le_right (by linarith) he)

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms

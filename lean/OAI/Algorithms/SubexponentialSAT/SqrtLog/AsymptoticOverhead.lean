import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.AsymptoticSchedule

namespace OAI.Algorithms

/-! Absorption of all fixed polylogarithmic exponents. The quantifiers keep
the power and multiplicative constant independent of the input size. -/

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

theorem schedule_shift_le (n : ℕ) : (s n : ℝ) + 2 ≤ 3 * logSize n := by
  have ht := four_le_logSize n
  have hs : (s n : ℝ) ≤ L n := by exact_mod_cast s_le_L n
  have hL := L_le_twice_logSize n
  linarith

theorem eventually_schedule_power_le_n (q : ℕ) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, C * ((s n : ℝ) + 2) ^ q ≤ n := by
  have hb := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (SubexpRuntime.eventually_logb_power_le q
      (show 0 < C * (3 : ℝ) ^ q by positivity))
  filter_upwards [hb] with n hn
  calc
    C * ((s n : ℝ) + 2) ^ q ≤ C * (3 * logSize n) ^ q :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (schedule_shift_le n) q) hC.le
    _ = (C * (3 : ℝ) ^ q) * logSize n ^ q := by rw [mul_pow]; ring
    _ ≤ n := hn

theorem eventually_polynomial_schedule_le_n (f : ℕ → ℕ)
    (hf : SparsificationConstants.PolynomialBound f) :
    ∀ᶠ n : ℕ in atTop, f (s n) ≤ n := by
  obtain ⟨q, hq⟩ := QuantitativeSparsify.polynomialBound_shift_power hf
  filter_upwards [eventually_schedule_power_le_n q (show (0 : ℝ) < 1 by norm_num)] with n hn
  have hfn : (f (s n) : ℝ) ≤ ((s n : ℝ) + 2) ^ q := by exact_mod_cast hq (s n)
  have hn' : ((s n : ℝ) + 2) ^ q ≤ n := by simpa only [one_mul] using hn
  have h : (f (s n) : ℝ) ≤ n := hfn.trans hn'
  exact_mod_cast h

theorem eventually_w_power_le_L (q : ℕ) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, C * (w n : ℝ) ^ q ≤ L n := by
  have hb := logSize_tendsto.eventually
    (SubexpRuntime.eventually_logb_power_le q
      (show 0 < C * (2 : ℝ) ^ q by positivity))
  filter_upwards [hb] with n hn
  have hm : logLogSize n ≤ Real.logb 2 (logSize n + 16) :=
    Real.logb_le_logb_of_le (by norm_num)
      (by have := four_le_logSize n; linarith) (by linarith)
  have hw : (w n : ℝ) ≤ 2 * Real.logb 2 (logSize n + 16) :=
    (w_le_twice_logLogSize n).trans (by linarith)
  calc
    C * (w n : ℝ) ^ q ≤ C * (2 * Real.logb 2 (logSize n + 16)) ^ q :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hw q) hC.le
    _ = (C * (2 : ℝ) ^ q) * Real.logb 2 (logSize n + 16) ^ q := by
      rw [mul_pow]; ring
    _ ≤ logSize n := hn
    _ ≤ L n := (logSize_lt_L n).le

theorem eventually_L_power_le_n (q : ℕ) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, C * (L n : ℝ) ^ q ≤ n := by
  have hb := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (SubexpRuntime.eventually_logb_power_le q
      (show 0 < C * (2 : ℝ) ^ q by positivity))
  filter_upwards [hb] with n hn
  calc
    C * (L n : ℝ) ^ q ≤ C * (2 * logSize n) ^ q :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (L_le_twice_logSize n) q) hC.le
    _ = (C * (2 : ℝ) ^ q) * logSize n ^ q := by rw [mul_pow]; ring
    _ ≤ n := hn

theorem eventually_logSize_power_le (q : ℕ) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, C * logSize n ^ q ≤ binaryScale n := by
  have hmain := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (SubexpRuntime.eventually_logb_power_le (q + 1) hC)
  filter_upwards [hmain] with n hn
  have ht := four_le_logSize n
  have hW := two_le_logLogSize n
  have ht0 : 0 < Real.sqrt (logSize n) := Real.sqrt_pos.2 (by linarith)
  have hroot : Real.sqrt (logSize n) ≤ logSize n := by
    apply Real.sqrt_le_iff.2
    constructor <;> nlinarith
  have hprod : C * logSize n ^ q * Real.sqrt (logSize n) ≤
      (n : ℝ) * logLogSize n ^ 2 := by
    calc
      C * logSize n ^ q * Real.sqrt (logSize n) ≤
          C * logSize n ^ q * logSize n :=
        mul_le_mul_of_nonneg_left hroot (by positivity)
      _ = C * logSize n ^ (q + 1) := by rw [pow_succ]; ring
      _ ≤ n := hn
      _ ≤ (n : ℝ) * logLogSize n ^ 2 := by
        have := Nat.cast_nonneg (α := ℝ) n
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ n by positivity)
          (show 0 ≤ logLogSize n ^ 2 - 1 by nlinarith)]
  exact (le_div_iff₀ ht0).2 hprod

theorem eventually_schedule_search_exponent (q : ℕ) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop,
      C * ((s n : ℝ) + 2) ^ q * Real.logb 2 ((n : ℝ) + 1) ≤ binaryScale n := by
  have hmain := eventually_logSize_power_le (q + 1)
    (show 0 < C * (3 : ℝ) ^ q by positivity)
  filter_upwards [hmain] with n hn
  have ht := four_le_logSize n
  have hs : (s n : ℝ) ≤ 2 * logSize n :=
    (by exact_mod_cast s_le_L n : (s n : ℝ) ≤ L n).trans (L_le_twice_logSize n)
  have hp := pow_le_pow_left₀ (show (0 : ℝ) ≤ (s n : ℝ) + 2 by positivity)
    (show (s n : ℝ) + 2 ≤ 3 * logSize n by linarith) q
  have hl : Real.logb 2 ((n : ℝ) + 1) ≤ logSize n :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) (by linarith)
  have hl0 : 0 ≤ Real.logb 2 ((n : ℝ) + 1) :=
    Real.logb_nonneg (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  calc
    C * ((s n : ℝ) + 2) ^ q * Real.logb 2 ((n : ℝ) + 1) ≤
        C * (3 * logSize n) ^ q * logSize n :=
      mul_le_mul (mul_le_mul_of_nonneg_left hp hC.le) hl hl0 (by positivity)
    _ = (C * (3 : ℝ) ^ q) * logSize n ^ (q + 1) := by
      rw [mul_pow, pow_succ]; ring
    _ ≤ binaryScale n := hn

theorem eventually_variable_degree_search (degree : ℕ → ℕ) (q : ℕ)
    {C : ℝ} (hC : 0 < C)
    (hdegree : ∀ᶠ n : ℕ in atTop, (degree n : ℝ) ≤ C * ((s n : ℝ) + 2) ^ q) :
    ∀ᶠ n : ℕ in atTop,
      (((n + 1) ^ degree n : ℕ) : ℝ) ≤ (2 : ℝ) ^ binaryScale n := by
  filter_upwards [hdegree, eventually_schedule_search_exponent q hC] with n hd hn
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

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms

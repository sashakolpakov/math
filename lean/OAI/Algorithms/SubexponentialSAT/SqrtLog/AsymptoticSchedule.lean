import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpRuntime

namespace OAI.Algorithms

/-! Exact, computable square-root-log scheduling. No algorithmic assertion is
hidden in these numerical lemmas. Small inputs may have schedule zero. -/

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

noncomputable def logSize (n : ℕ) : ℝ := Real.logb 2 ((n : ℝ) + 16)
noncomputable def logLogSize (n : ℕ) : ℝ := Real.logb 2 (logSize n)
noncomputable def binaryScale (n : ℕ) : ℝ :=
  (n : ℝ) * logLogSize n ^ 2 / Real.sqrt (logSize n)

def L (n : ℕ) : ℕ := Nat.log2 (n + 16) + 1
def w (n : ℕ) : ℕ := Nat.log2 (L n) + 1
def s (n : ℕ) : ℕ := Nat.sqrt (L n) / w n ^ 2

theorem w_pos (n : ℕ) : 0 < w n := by unfold w; omega
theorem L_pos (n : ℕ) : 0 < L n := by unfold L; omega

theorem le_s_iff (n a : ℕ) : a ≤ s n ↔ a ^ 2 * w n ^ 4 ≤ L n := by
  rw [s, Nat.le_div_iff_mul_le (pow_pos (w_pos n) 2), Nat.le_sqrt']
  ring_nf

theorem schedule_feasible (n : ℕ) : s n ^ 2 * w n ^ 4 ≤ L n :=
  (le_s_iff n (s n)).mp le_rfl

theorem schedule_maximal (n : ℕ) : L n < (s n + 1) ^ 2 * w n ^ 4 := by
  have h := (le_s_iff n (s n + 1)).not
  exact Nat.lt_of_not_ge (h.mp (by omega))

theorem s_le_L (n : ℕ) : s n ≤ L n :=
  (Nat.div_le_self _ _).trans (Nat.sqrt_le_self _)

theorem four_le_logSize (n : ℕ) : 4 ≤ logSize n := by
  apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : 0 < (n : ℝ) + 16)).mpr
  norm_num

theorem two_le_logLogSize (n : ℕ) : 2 ≤ logLogSize n := by
  apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2)
    (by have := four_le_logSize n; linarith : 0 < logSize n)).mpr
  norm_num
  exact four_le_logSize n

theorem logSize_lt_L (n : ℕ) : logSize n < (L n : ℝ) := by
  simpa [logSize, L, Nat.cast_add, Nat.cast_ofNat] using
    SubexpExponentArithmetic.logb_lt_natLog2_add_one (n + 16)

theorem L_le_logSize_add_one (n : ℕ) : (L n : ℝ) ≤ logSize n + 1 := by
  have h := Real.natLog_le_logb (n + 16) 2
  simpa [L, logSize, Nat.log2_eq_log_two, Nat.cast_add] using add_le_add_right h 1

theorem L_le_twice_logSize (n : ℕ) : (L n : ℝ) ≤ 2 * logSize n := by
  have := L_le_logSize_add_one n
  have := four_le_logSize n
  linarith

theorem logLogSize_lt_w (n : ℕ) : logLogSize n < (w n : ℝ) := by
  have h := SubexpExponentArithmetic.logb_lt_natLog2_add_one (L n)
  have hm : logLogSize n ≤ Real.logb 2 (L n : ℝ) :=
    Real.logb_le_logb_of_le (by norm_num) (by have := four_le_logSize n; linarith)
      (logSize_lt_L n).le
  exact hm.trans_lt (by simpa [w] using h)

theorem w_le_twice_logLogSize (n : ℕ) : (w n : ℝ) ≤ 2 * logLogSize n := by
  have hp : (0 : ℝ) < logSize n := by have := four_le_logSize n; linarith
  have hL : (0 : ℝ) < L n := by exact_mod_cast L_pos n
  have hn := Real.natLog_le_logb (L n) 2
  have hlog : Real.logb 2 (L n : ℝ) ≤ 1 + logLogSize n := by
    calc
      Real.logb 2 (L n : ℝ) ≤ Real.logb 2 (2 * logSize n) :=
        Real.logb_le_logb_of_le (by norm_num) hL (L_le_twice_logSize n)
      _ = 1 + logLogSize n := by
        rw [Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0) hp.ne']
        norm_num [logLogSize]
  have hw : (w n : ℝ) ≤ Real.logb 2 (L n : ℝ) + 1 := by
    simpa [w, Nat.log2_eq_log_two] using add_le_add_right hn 1
  have := two_le_logLogSize n
  linarith

theorem logSize_tendsto : Tendsto logSize atTop atTop := by
  exact (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds)

theorem eventually_le_s (a : ℕ) : ∀ᶠ n : ℕ in atTop, a ≤ s n := by
  have hb := logSize_tendsto.eventually
    (SubexpRuntime.eventually_logb_power_le 4
      (show (0 : ℝ) < ((a : ℝ) + 1) ^ 2 * 16 by positivity))
  filter_upwards [hb] with n hn
  have hw : (w n : ℝ) ≤ 2 * Real.logb 2 (logSize n + 16) := by
    have hm : logLogSize n ≤ Real.logb 2 (logSize n + 16) :=
      Real.logb_le_logb_of_le (by norm_num)
        (by have := four_le_logSize n; linarith) (by linarith)
    exact (w_le_twice_logLogSize n).trans (by linarith)
  have hp := pow_le_pow_left₀ (show (0 : ℝ) ≤ w n by positivity) hw 4
  have ha : (a : ℝ) ^ 2 * (w n : ℝ) ^ 4 ≤ (L n : ℝ) := by
    calc
      (a : ℝ) ^ 2 * (w n : ℝ) ^ 4 ≤
          ((a : ℝ) + 1) ^ 2 * (2 * Real.logb 2 (logSize n + 16)) ^ 4 := by
        apply mul_le_mul
        · nlinarith [Nat.cast_nonneg (α := ℝ) a]
        · exact hp
        · positivity
        · positivity
      _ = (((a : ℝ) + 1) ^ 2 * 16) * Real.logb 2 (logSize n + 16) ^ 4 := by ring_nf
      _ ≤ logSize n := hn
      _ ≤ (L n : ℝ) := (logSize_lt_L n).le
  exact (le_s_iff n a).mpr (by exact_mod_cast ha)

theorem s_tendsto : Tendsto s atTop atTop := tendsto_atTop.2 eventually_le_s

theorem schedule_upper (n : ℕ) :
    (s n : ℝ) ≤ 2 * Real.sqrt (logSize n) / logLogSize n ^ 2 := by
  have ht := four_le_logSize n
  have hW := two_le_logLogSize n
  have hs0 : (0 : ℝ) ≤ s n := by positivity
  have hw0 : (0 : ℝ) ≤ w n := by positivity
  have hfeas : (s n : ℝ) ^ 2 * (w n : ℝ) ^ 4 ≤ (L n : ℝ) := by
    exact_mod_cast schedule_feasible n
  have hw := logLogSize_lt_w n
  have hsq : logLogSize n ^ 2 ≤ (w n : ℝ) ^ 2 := by nlinarith
  have hr0 := Real.sqrt_nonneg (logSize n)
  have hroot := Real.sq_sqrt (show 0 ≤ logSize n by linarith)
  have hprod : (s n : ℝ) * (w n : ℝ) ^ 2 ≤ 2 * Real.sqrt (logSize n) := by
    have hprod0 : 0 ≤ (s n : ℝ) * (w n : ℝ) ^ 2 := by positivity
    have hp : ((s n : ℝ) * (w n : ℝ) ^ 2) ^ 2 ≤ 2 * logSize n := by
      calc
        _ = (s n : ℝ) ^ 2 * (w n : ℝ) ^ 4 := by ring_nf
        _ ≤ (L n : ℝ) := hfeas
        _ ≤ 2 * logSize n := L_le_twice_logSize n
    nlinarith
  apply (le_div_iff₀ (sq_pos_of_pos (show 0 < logLogSize n by linarith))).2
  exact (mul_le_mul_of_nonneg_left hsq hs0).trans hprod

/-- An explicit lower-bound comparison, with the only small-input condition
being positivity of the actual integer schedule. -/
theorem sqrt_logSize_le (n : ℕ) (hs : 1 ≤ s n) :
    Real.sqrt (logSize n) ≤ 8 * (s n : ℝ) * logLogSize n ^ 2 := by
  have ht := four_le_logSize n
  have hW := two_le_logLogSize n
  have hs' : (1 : ℝ) ≤ s n := by exact_mod_cast hs
  have hm : (L n : ℝ) < ((s n : ℝ) + 1) ^ 2 * (w n : ℝ) ^ 4 := by
    exact_mod_cast schedule_maximal n
  have hroot := Real.sq_sqrt (show 0 ≤ logSize n by linarith)
  have hr0 := Real.sqrt_nonneg (logSize n)
  have hw0 : (0 : ℝ) ≤ w n := by positivity
  have hw := w_le_twice_logLogSize n
  have hw2 : (w n : ℝ) ^ 2 ≤ 4 * logLogSize n ^ 2 := by nlinarith
  have hfirst : Real.sqrt (logSize n) ≤ ((s n : ℝ) + 1) * (w n : ℝ) ^ 2 := by
    apply Real.sqrt_le_iff.2
    refine ⟨by positivity, ?_⟩
    calc
      logSize n ≤ (L n : ℝ) := (logSize_lt_L n).le
      _ ≤ ((s n : ℝ) + 1) ^ 2 * (w n : ℝ) ^ 4 := hm.le
      _ = (((s n : ℝ) + 1) * (w n : ℝ) ^ 2) ^ 2 := by ring_nf
  have hmul := mul_le_mul_of_nonneg_left hw2 (show 0 ≤ (s n : ℝ) + 1 by positivity)
  nlinarith [sq_nonneg (logLogSize n)]

theorem inverse_schedule_le (n : ℕ) (hs : 1 ≤ s n) :
    (n : ℝ) / s n ≤ 8 * binaryScale n := by
  have hs' : (0 : ℝ) < s n := by exact_mod_cast (by omega : 0 < s n)
  have ht : 0 < Real.sqrt (logSize n) :=
    Real.sqrt_pos.2 (by have := four_le_logSize n; linarith)
  have h := mul_le_mul_of_nonneg_left (sqrt_logSize_le n hs) (Nat.cast_nonneg n)
  unfold binaryScale
  rw [show 8 * ((n : ℝ) * logLogSize n ^ 2 / Real.sqrt (logSize n)) =
    (8 * (n : ℝ) * logLogSize n ^ 2) / Real.sqrt (logSize n) by ring_nf]
  apply (div_le_div_iff₀ hs' ht).2
  convert h using 1
  ring_nf

theorem eventually_inverse_schedule_le :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) / s n ≤ 8 * binaryScale n := by
  filter_upwards [eventually_le_s 1] with n hn
  exact inverse_schedule_le n hn

/-- Both comparisons have absolute constants; the lower bound is eventual
because the exact integer schedule is deliberately allowed to be zero. -/
theorem eventually_schedule_comparison :
    ∀ᶠ n : ℕ in atTop,
      Real.sqrt (logSize n) / (8 * logLogSize n ^ 2) ≤ (s n : ℝ) ∧
      (s n : ℝ) ≤ 2 * Real.sqrt (logSize n) / logLogSize n ^ 2 := by
  filter_upwards [eventually_le_s 1] with n hn
  refine ⟨?_, schedule_upper n⟩
  have hW := two_le_logLogSize n
  apply (div_le_iff₀ (show 0 < 8 * logLogSize n ^ 2 by positivity)).2
  nlinarith [sqrt_logSize_le n hn]

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms

import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.BranchTree
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SupportProgramCount
import OAI.Algorithms.SubexponentialSAT.SqrtLog.AsymptoticLayoutCost

namespace OAI.Algorithms

/-! Exact squarefree support entropy at the square-root-log scale.  The
hypothesis on J is a numerical jet-order bound, not a support-count oracle. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly

open Filter
open scoped Topology BigOperators
open Asymptotic

noncomputable def entropyCutoff (n : ℕ) (C : ℝ) : ℝ :=
  C * n * w n / Real.sqrt (L n : ℝ)

/-- The extra logarithm in support entropy is exactly the second w factor. -/
theorem weighted_scale_le_target (n : ℕ) :
    (n : ℝ) * (w n : ℝ)^2 / Real.sqrt (L n : ℝ) ≤
      64 * Statement.runtimeScale n := by
  have ht := four_le_logSize n
  have hroots : Real.sqrt (logSize n) ≤ Real.sqrt (L n : ℝ) :=
    Real.sqrt_le_sqrt (logSize_lt_L n).le
  have hw := w_le_twice_logLogSize n
  have hfirst : (n : ℝ) * (w n : ℝ)^2 / Real.sqrt (L n : ℝ) ≤
      4 * binaryScale n := by
    calc
      _ ≤ (n : ℝ) * (2 * logLogSize n)^2 / Real.sqrt (logSize n) := by
        gcongr
      _ = _ := by unfold binaryScale; ring
  linarith [binaryScale_le_target n]

theorem log_four_L_le (n : ℕ) :
    Real.log (4 * (L n : ℝ)) ≤ 3 * (w n : ℝ) := by
  have hL : (0 : ℝ) < L n := by exact_mod_cast L_pos n
  have hw : (1 : ℝ) ≤ w n := by exact_mod_cast w_pos n
  have hlog : Real.log (L n : ℝ) ≤ (w n : ℝ) := by
    have h := SubexpExponentArithmetic.logb_lt_natLog2_add_one (L n)
    have h' : Real.log (L n : ℝ) / Real.log 2 < (w n : ℝ) := by
      simpa [Real.logb, w, Nat.cast_add, Nat.cast_one] using h
    have h2 := log_two_bounds
    have hmul := (div_lt_iff₀ (show 0 < Real.log 2 by linarith)).mp h'
    nlinarith
  have hfour : Real.log (4 : ℝ) ≤ 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith [log_two_bounds]
  rw [Real.log_mul (by norm_num) hL.ne']
  linarith

/-- Pointwise entropy bound, using any positive real upper cutoff. -/
theorem support_le_entropy (n J : ℕ) {u : ℝ}
    (hu : 0 < u) (hun : u ≤ n) (hJu : (J : ℝ) ≤ u)
    (hlo : (n : ℝ) / Real.sqrt (L n : ℝ) ≤ u) :
    (SupportProgram.count n J : ℝ) ≤
      (J : ℝ) * (2 : ℝ) ^ (6 * u * w n) := by
  have hL : (0 : ℝ) < L n := by exact_mod_cast L_pos n
  have hL1 : (1 : ℝ) ≤ L n := by exact_mod_cast L_pos n
  have hsqrt : Real.sqrt (L n : ℝ) ≤ (L n : ℝ) :=
    (Real.sqrt_le_iff).mpr ⟨hL.le, by nlinarith⟩
  have hroot : 0 < Real.sqrt (L n : ℝ) := Real.sqrt_pos.2 hL
  have hn : (0 : ℝ) < n := hu.trans_le hun
  have hratio : 4 * (n : ℝ) / u ≤ 4 * (L n : ℝ) := by
    have hh := (div_le_iff₀ hroot).mp hlo
    have hh' : (n : ℝ) ≤ u * (L n : ℝ) :=
      hh.trans (mul_le_mul_of_nonneg_left hsqrt hu.le)
    apply (div_le_iff₀ hu).mpr
    nlinarith
  have hlog : Real.log (4 * (n : ℝ) / u) ≤ 3 * (w n : ℝ) :=
    (Real.log_le_log (by positivity) hratio).trans (log_four_L_le n)
  have hbudget : u * Real.log (4 * (n : ℝ) / u) ≤
      Real.log 2 * (6 * u * w n) := by
    have hh := mul_le_mul_of_nonneg_left hlog hu.le
    have h2 := log_two_bounds
    have hw : (0 : ℝ) ≤ w n := by positivity
    nlinarith [mul_nonneg hu.le hw]
  have hpow : (4 * (n : ℝ) / u)^u ≤ (2 : ℝ)^(6 * u * w n) := by
    rw [Real.rpow_def_of_pos (by positivity),
      Real.rpow_def_of_pos (by norm_num), Real.exp_le_exp]
    nlinarith [hbudget]
  unfold SupportProgram.count
  push_cast
  calc
    ∑ j ∈ Finset.range J, (n.choose j : ℝ) ≤
        ∑ _j ∈ Finset.range J, (2 : ℝ)^(6 * u * w n) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' : (j : ℝ) ≤ u :=
        (Nat.cast_le.mpr (Nat.le_of_lt (Finset.mem_range.mp hj))).trans hJu
      exact (SubexponentialSAT.BranchTree.choose_le_rpow_real n j hu hun hj').trans hpow
    _ = _ := by simp

/-- All constants are explicit except the finite threshold. -/
theorem eventually_support_target (J : ℕ → ℕ) {C : ℝ} (hC : 1 ≤ C)
    (hJ : ∀ᶠ n : ℕ in atTop, (J n : ℝ) ≤ entropyCutoff n C) :
    ∀ᶠ n : ℕ in atTop, (SupportProgram.count n (J n) : ℝ) ≤
      (2 : ℝ)^((384 * C + 1) * Statement.runtimeScale n) := by
  have hCpos : 0 < C := by linarith
  have hsmall := eventually_w_power_le_L 2 (sq_pos_of_pos hCpos)
  have hpoly := eventually_polylog_le_target 1 (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hJ, hsmall, hpoly, eventually_ge_atTop 1] with n hJ hnsmall hnpoly hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hw : (1 : ℝ) ≤ w n := by exact_mod_cast w_pos n
  have hL : (0 : ℝ) < L n := by exact_mod_cast L_pos n
  have hr : 0 < Real.sqrt (L n : ℝ) := Real.sqrt_pos.2 hL
  have hcw : C * (w n : ℝ) ≤ Real.sqrt (L n : ℝ) := by
    apply (Real.le_sqrt (by positivity) hL.le).2
    nlinarith [hnsmall]
  have hu : 0 < entropyCutoff n C := by unfold entropyCutoff; positivity
  have hun : entropyCutoff n C ≤ n := by
    unfold entropyCutoff
    apply (div_le_iff₀ hr).2
    nlinarith
  have hlo : (n : ℝ) / Real.sqrt (L n : ℝ) ≤ entropyCutoff n C := by
    unfold entropyCutoff
    apply div_le_div_of_nonneg_right _ hr.le
    have hc := mul_le_mul hC hw (by norm_num : (0 : ℝ) ≤ 1) hCpos.le
    nlinarith
  have hmain := support_le_entropy n (J n) hu hun hJ hlo
  have hcost : 6 * entropyCutoff n C * w n ≤
      384 * C * Statement.runtimeScale n := by
    have hh := mul_le_mul_of_nonneg_left (weighted_scale_le_target n) (show 0 ≤ 6*C by positivity)
    unfold entropyCutoff
    convert hh using 1 <;> ring
  have hJn : (J n : ℝ) ≤ n := hJ.trans hun
  have hnexp : (n : ℝ) ≤ (2 : ℝ)^Statement.runtimeScale n := by
    have hlog : logSize n ≤ Statement.runtimeScale n := by simpa using hnpoly
    calc
      (n : ℝ) ≤ (n : ℝ) + 16 := by linarith
      _ = (2 : ℝ)^logSize n := by
        symm
        exact Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hlog
  calc
    (SupportProgram.count n (J n) : ℝ) ≤
        (J n : ℝ) * (2 : ℝ)^(6 * entropyCutoff n C * w n) := hmain
    _ ≤ (2 : ℝ)^Statement.runtimeScale n *
        (2 : ℝ)^(384*C*Statement.runtimeScale n) := by
      exact mul_le_mul (hJn.trans hnexp)
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hcost)
        (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by norm_num) _)
    _ = _ := by rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms

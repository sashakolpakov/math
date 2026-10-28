import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.AsymptoticLayoutRate

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

private theorem label_log_bound (N B Q : ℝ) (R : ℕ)
    (hN : 1 ≤ N) (hB : 1 ≤ B) (hQ : 1 ≤ Q) :
    Real.log (4 * N * B * (8 * Q) ^ (2 * R) + 1) ≤
      7 + Real.log N + Real.log B + (2 * R : ℕ) * (7 + Real.log Q) := by
  have hN0 : 0 < N := by linarith
  have hB0 : 0 < B := by linarith
  have hQ0 : 0 < Q := by linarith
  have hp : 1 ≤ (8 * Q) ^ (2 * R) := one_le_pow₀ (by linarith)
  have hz : 1 ≤ 4 * N * B * (8 * Q) ^ (2 * R) := by
    have hNB := one_le_mul_of_one_le_of_one_le hN hB
    have hNBp := one_le_mul_of_one_le_of_one_le hNB hp
    nlinarith
  have hlog8 : Real.log 8 ≤ 7 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)
    linarith
  calc
    Real.log (4 * N * B * (8 * Q) ^ (2 * R) + 1) ≤
        Real.log (8 * N * B * (8 * Q) ^ (2 * R)) :=
      Real.log_le_log (by positivity) (by nlinarith)
    _ = Real.log 8 + Real.log N + Real.log B +
        (2 * R : ℕ) * (Real.log 8 + Real.log Q) := by
      simp [Real.log_mul, Real.log_pow, hN0.ne', hB0.ne', hQ0.ne']
    _ ≤ 7 + Real.log N + Real.log B + (2 * R : ℕ) * (7 + Real.log Q) := by gcongr

theorem eventually_layout_label_log (b : ℕ → ℕ) (q : ℕ)
    (hb : ∀ᶠ n : ℕ in atTop, 1 ≤ b n ∧ b n ≤ L n ^ q) :
    ∀ᶠ n : ℕ in atTop,
      Real.log (4 * (n : ℝ) * b n * (8 * (layoutQ n : ℝ)) ^
        (2 * layoutCutoff n (b n)) + 1) ≤ 4 * (L n : ℝ) ^ 2 := by
  have hbp : ∀ᶠ n : ℕ in atTop, b n ≤ L n ^ q := hb.mono fun _ h => h.2
  filter_upwards [hb, eventually_layout_fits b q hbp, eventually_layoutQ_ge 1,
    eventually_L_ge (max 16 q), eventually_ge_atTop (1 : ℕ)] with n hbn hfit hQ hL hn
  have hL16 : (16 : ℝ) ≤ L n := by exact_mod_cast (le_max_left 16 q).trans hL
  have hqL : (q : ℝ) ≤ L n := by exact_mod_cast (le_max_right 16 q).trans hL
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hB : (1 : ℝ) ≤ b n := by exact_mod_cast hbn.1
  have hQ' : (1 : ℝ) ≤ layoutQ n := by exact_mod_cast hQ
  have hR : (layoutCutoff n (b n) : ℝ) ≤ L n := by
    have hQle : layoutQ n ≤ L n := Nat.div_le_self _ _
    exact_mod_cast (show layoutCutoff n (b n) ≤ L n by omega)
  have hLn : Real.log (n : ℝ) ≤ L n := by
    calc
      Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 16) := Real.log_le_log (by linarith) (by linarith)
      _ ≤ logSize n := (logSize_natural_bounds n).1
      _ ≤ L n := (logSize_lt_L n).le
  have hLL : Real.log (L n : ℝ) ≤ L n := by
    have h := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < L n)
    linarith
  have hLB : Real.log (b n : ℝ) ≤ (q : ℝ) * (L n : ℝ) := by
    calc
      Real.log (b n : ℝ) ≤ Real.log ((L n : ℝ) ^ q) :=
        Real.log_le_log (by linarith) (by exact_mod_cast hbn.2)
      _ = (q : ℝ) * Real.log (L n : ℝ) := Real.log_pow _ _
      _ ≤ (q : ℝ) * (L n : ℝ) := mul_le_mul_of_nonneg_left hLL (Nat.cast_nonneg q)
  have hLQ : Real.log (layoutQ n : ℝ) ≤ L n := by
    calc
      Real.log (layoutQ n : ℝ) ≤ Real.log (L n : ℝ) :=
        Real.log_le_log (by linarith) (by exact_mod_cast Nat.div_le_self (L n) (layoutDen n))
      _ ≤ L n := hLL
  have hmain := label_log_bound (n : ℝ) (b n : ℝ) (layoutQ n : ℝ)
    (layoutCutoff n (b n)) hN hB hQ'
  have hprod : (2 * layoutCutoff n (b n) : ℕ) * (7 + Real.log (layoutQ n : ℝ)) ≤
      2 * (L n : ℝ) * (7 + (L n : ℝ)) := by
    push_cast
    gcongr
  have hqb := mul_le_mul_of_nonneg_right hqL (show (0 : ℝ) ≤ L n by positivity)
  nlinarith

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms

import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.AsymptoticLayoutRate

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

theorem eventually_layout_small_grid :
    ∀ᶠ n : ℕ in atTop, 16 * layoutQ n * layoutR n ^ 2 ≤ n := by
  filter_upwards [eventually_L_power_le_n 3 (show (0 : ℝ) < 16 by norm_num)] with n hn
  have hnat : 16 * L n ^ 3 ≤ n := by exact_mod_cast hn
  have hQ : layoutQ n ≤ L n := Nat.div_le_self _ _
  have hr := layoutR_le_L n
  calc
    16 * layoutQ n * layoutR n ^ 2 ≤ 16 * L n * L n ^ 2 := by gcongr
    _ = 16 * L n ^ 3 := by ring
    _ ≤ n := hnat

theorem eventually_layout_large_grid (a b : ℕ → ℕ) (q : ℕ)
    (ha : ∀ᶠ n : ℕ in atTop, a n ≤ L n ^ q)
    (hb : ∀ᶠ n : ℕ in atTop, b n ≤ L n ^ q) :
    ∀ᶠ n : ℕ in atTop,
      4096 * (b n + a n) * b n ^ 2 * layoutR n ^ 2 * L n ^ 4 *
        (layoutR n ^ (2 * layoutQ n)) ^ 2 ≤ n := by
  let f (n : ℕ) : ℝ := 4096 * ((b n : ℝ) + a n) * (b n : ℝ) ^ 2 *
    (layoutR n : ℝ) ^ 2 * (L n : ℝ) ^ 4
  have hf : ∀ᶠ n : ℕ in atTop, f n ≤ 8192 * (L n : ℝ) ^ (3 * q + 6) := by
    filter_upwards [ha, hb] with n han hbn
    have ha' : (a n : ℝ) ≤ (L n : ℝ) ^ q := by exact_mod_cast han
    have hb' : (b n : ℝ) ≤ (L n : ℝ) ^ q := by exact_mod_cast hbn
    have hr : (layoutR n : ℝ) ≤ L n := by exact_mod_cast layoutR_le_L n
    calc
      f n ≤ 4096 * ((L n : ℝ) ^ q + (L n : ℝ) ^ q) * ((L n : ℝ) ^ q) ^ 2 *
          (L n : ℝ) ^ 2 * (L n : ℝ) ^ 4 := by dsimp [f]; gcongr
      _ = 8192 * (L n : ℝ) ^ (3 * q + 6) := by
        simp only [pow_add, pow_mul]
        ring
  have h := eventually_polylog_grid_le_n f (3 * q + 6)
    (show (0 : ℝ) < 8192 by norm_num) (by intro n; dsimp [f]; positivity) hf
  filter_upwards [h] with n hn
  have heq : (layoutR n ^ (2 * layoutQ n)) ^ 2 = layoutR n ^ (4 * layoutQ n) := by
    rw [← pow_mul]
    congr 1
    omega
  rw [heq]
  dsimp [f] at hn
  exact_mod_cast hn

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms

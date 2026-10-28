import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.AsymptoticLayoutParameters

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

theorem layoutR_le_L (n : ℕ) : layoutR n ≤ L n := by
  have h : (4 : ℝ) < L n := (four_le_logSize n).trans_lt (logSize_lt_L n)
  have hnat : 4 < L n := by exact_mod_cast h
  exact max_le (by omega) (s_le_L n)

theorem layoutDen_le (n : ℕ) : layoutDen n ≤ 64 * w n := by
  have h := Nat.log_mono_right (b := 2) (layoutR_le_L n)
  simpa only [layoutDen, w, Nat.log2_eq_log_two] using Nat.mul_le_mul_left 64
    (Nat.add_le_add_right h 1)

theorem layoutEnergy_le (n b q : ℕ) (hb : b ≤ L n ^ q) :
    layoutEnergy n b ≤ (q + 10) * w n := by
  have hL : L n ≤ 2 ^ w n := (Nat.lt_log2_self (n := L n)).le
  have hr := layoutR_le_L n
  have hz : 64 * b * layoutR n * L n ^ 2 ≤ 2 ^ (6 + w n * (q + 3)) := by
    calc
      64 * b * layoutR n * L n ^ 2 ≤ 64 * (L n ^ q) * L n * L n ^ 2 := by gcongr
      _ = 64 * L n ^ (q + 3) := by ring
      _ ≤ 64 * (2 ^ w n) ^ (q + 3) := by gcongr
      _ = 2 ^ (6 + w n * (q + 3)) := by rw [← pow_mul]; norm_num [pow_add]
  have hlog := Nat.log_mono_right (b := 2) hz
  rw [Nat.log_pow (by norm_num : 1 < (2 : ℕ))] at hlog
  have hw := w_pos n
  unfold layoutEnergy
  rw [Nat.log2_eq_log_two]
  nlinarith

theorem eventually_layoutQ_ge (a : ℕ) : ∀ᶠ n : ℕ in atTop, a ≤ layoutQ n := by
  have hh := eventually_w_power_le_L 1 (show (0 : ℝ) < 64 * ((a : ℝ) + 1) by positivity)
  filter_upwards [hh] with n hn
  simp only [pow_one] at hn
  have hh' : 64 * (a + 1) * w n ≤ L n := by exact_mod_cast hn
  have hd := layoutDen_le n
  apply (Nat.le_div_iff_mul_le (layoutDen_pos n)).2
  nlinarith

theorem eventually_layoutQ_energy_ratio (b : ℕ → ℕ) (q A : ℕ)
    (hb : ∀ᶠ n : ℕ in atTop, b n ≤ L n ^ q) :
    ∀ᶠ n : ℕ in atTop, A * layoutEnergy n (b n) ≤ layoutQ n := by
  have hh := eventually_w_power_le_L 2
    (show (0 : ℝ) < 64 * ((A : ℝ) + 1) * ((q : ℝ) + 10) by positivity)
  filter_upwards [hb, hh] with n hn hpow
  have hp : 64 * (A + 1) * (q + 10) * w n ^ 2 ≤ L n := by exact_mod_cast hpow
  have he := layoutEnergy_le n (b n) q hn
  have hd := layoutDen_le n
  apply (Nat.le_div_iff_mul_le (layoutDen_pos n)).2
  calc
    A * layoutEnergy n (b n) * layoutDen n ≤ A * ((q + 10) * w n) * (64 * w n) := by gcongr
    _ ≤ 64 * (A + 1) * (q + 10) * w n ^ 2 := by nlinarith
    _ ≤ L n := hp

theorem layout_fits_of_ratio (n b : ℕ)
    (hQ : 64 ≤ layoutQ n) (he : 32768 * layoutEnergy n b ≤ layoutQ n) :
    4 * layoutCutoff n b ≤ layoutQ n := by
  have hs := Nat.sqrt_le' (128 * layoutQ n * layoutEnergy n b)
  unfold layoutCutoff
  nlinarith

theorem eventually_layout_fits (b : ℕ → ℕ) (q : ℕ)
    (hb : ∀ᶠ n : ℕ in atTop, b n ≤ L n ^ q) :
    ∀ᶠ n : ℕ in atTop, 4 * layoutCutoff n (b n) ≤ layoutQ n := by
  filter_upwards [eventually_layoutQ_ge 64,
    eventually_layoutQ_energy_ratio b q 32768 hb] with n hn he
  exact layout_fits_of_ratio n (b n) hn he

theorem layout_grid_square (n : ℕ) :
    (layoutR n ^ (4 * layoutQ n)) ^ 2 ≤ n + 16 := by
  have hbudget : 64 * (Nat.log2 (layoutR n) + 1) * layoutQ n ≤ L n := by
    exact Nat.mul_div_le (L n) (layoutDen n)
  have hlog : 1 ≤ Nat.log2 (n + 16) :=
    (Nat.le_log2 (by omega)).2 (by norm_num)
  have hexp : (Nat.log2 (layoutR n) + 1) * (4 * layoutQ n * 2) ≤ Nat.log2 (n + 16) := by
    unfold L at hbudget
    nlinarith
  calc
    (layoutR n ^ (4 * layoutQ n)) ^ 2 = layoutR n ^ (4 * layoutQ n * 2) :=
      (pow_mul _ _ _).symm
    _ ≤ (2 ^ (Nat.log2 (layoutR n) + 1)) ^ (4 * layoutQ n * 2) :=
      Nat.pow_le_pow_left (Nat.lt_log2_self.le) _
    _ = 2 ^ ((Nat.log2 (layoutR n) + 1) * (4 * layoutQ n * 2)) :=
      (pow_mul _ _ _).symm
    _ ≤ 2 ^ Nat.log2 (n + 16) := Nat.pow_le_pow_right (by omega) hexp
    _ ≤ n + 16 := Nat.log2_self_le (by omega)

/-- The exponentially many grid cells still leave room for every fixed
polylogarithmic factor. The exponent 4Q is the actual squared grid factor. -/
theorem eventually_polylog_grid_le_n (f : ℕ → ℝ) (q : ℕ) {C : ℝ} (hC : 0 < C)
    (hf0 : ∀ n, 0 ≤ f n)
    (hf : ∀ᶠ n : ℕ in atTop, f n ≤ C * (L n : ℝ) ^ q) :
    ∀ᶠ n : ℕ in atTop, f n * (layoutR n : ℝ) ^ (4 * layoutQ n) ≤ n := by
  have hh := eventually_L_power_le_n (2 * q) (show 0 < 2 * C ^ 2 by positivity)
  filter_upwards [hf, hh, eventually_ge_atTop (16 : ℕ)] with n hn hp hn16
  have hgrid : ((layoutR n : ℝ) ^ (4 * layoutQ n)) ^ 2 ≤ (n : ℝ) + 16 := by
    exact_mod_cast layout_grid_square n
  have hsq : 2 * (f n) ^ 2 ≤ n := by
    have hpow := pow_le_pow_left₀ (hf0 n) hn 2
    have heq : (C * (L n : ℝ) ^ q) ^ 2 = C ^ 2 * (L n : ℝ) ^ (2 * q) := by
      rw [mul_pow, ← pow_mul]
      congr 2
      omega
    rw [heq] at hpow
    nlinarith
  have hn16' : (16 : ℝ) ≤ n := by exact_mod_cast hn16
  have hmul := mul_le_mul hsq hgrid (sq_nonneg _) (by positivity : (0 : ℝ) ≤ n)
  have hfpos := hf0 n
  have hgpos : 0 ≤ (layoutR n : ℝ) ^ (4 * layoutQ n) := by positivity
  nlinarith [sq_nonneg ((n : ℝ) - f n * (layoutR n : ℝ) ^ (4 * layoutQ n))]

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
